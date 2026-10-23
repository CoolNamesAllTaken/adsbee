from datetime import timedelta
from io import StringIO

import pytest
from django.core.management import call_command
from django.test import override_settings
from django.utils import timezone

from adsbee_swarm import conf, protocol, queries, retention
from adsbee_swarm.models import Device, Sample
from adsbee_swarm.simulator import Bee

from .conftest import save_sample

pytestmark = pytest.mark.django_db


@pytest.fixture
def device(owner):
    return Device.objects.create(account=owner.account, product='adsbee_1090', unique_id='E6614C311B5B6F2A')


def _hour(device, start, values, unit=2000, protocol='aircraft', **stats):
    save_sample(Sample(device=device, start=start, reports=1, **stats), values, protocol, unit)


def _days(device):
    return list(Sample.objects.filter(device=device, span_s=Sample.DAY))


def test_hourly_rows_are_kept_90_days_and_daily_rows_forever():
    assert conf.get('HOURLY_RETENTION_DAYS') == 90 and conf.get('DAILY_RETENTION_DAYS') is None


def test_every_report_lands_in_its_hour_and_its_day(device):
    bee = Bee.make(0)
    start = timezone.now().replace(hour=3, minute=10, second=0, microsecond=0)
    first, second = bee.report(), bee.report()
    protocol.ingest(device, protocol.parse(first), start)
    protocol.ingest(device, protocol.parse(second), start + timedelta(hours=2))
    hours = Sample.objects.filter(device=device, span_s=Sample.HOUR)
    (day,) = _days(device)
    assert hours.count() == 2 and day.start == start.replace(hour=0, minute=0)
    assert day.reports == 2 and day.es_valid == first['stats']['es_valid'] + second['stats']['es_valid']
    assert day.aircraft_max == max(first['stats']['aircraft_max'], second['stats']['aircraft_max'])
    hourly_union = {}
    for hour in hours:
        for index, meters in hour.ranges().items():
            hourly_union[index] = max(hourly_union.get(index, 0), meters)
    assert day.ranges() == hourly_union


def test_a_widened_retry_does_not_count_twice_in_the_day(device):
    bee = Bee.make(1)
    body = bee.report()
    body['stats']['es_valid'] = 100
    now = timezone.now().replace(hour=5, minute=0)
    protocol.ingest(device, protocol.parse(body), now)
    widened = {**body, 'period': {**body['period'], 'len_s': body['period']['len_s'] + 900},
               'stats': {**body['stats'], 'es_valid': 140}}
    protocol.ingest(device, protocol.parse(widened), now + timedelta(minutes=20))
    (day,) = _days(device)
    assert (day.es_valid, day.reports) == (140, 1)
    assert retention.rebuild_day(device.pk, day.start, list(Sample.objects.filter(device=device, span_s=Sample.HOUR))) \
        is False, "the day already adds up"


def test_long_windows_read_days_and_short_ones_hours(device):
    now = timezone.now().replace(minute=0, second=0, microsecond=0)
    day = now.replace(hour=0) - timedelta(days=10)
    Sample.objects.create(device=device, start=day, span_s=Sample.DAY, es_valid=50)
    _hour(device, day + timedelta(hours=2), {7: 4000}, es_valid=50)
    save_sample(Sample(device=device, start=day + timedelta(days=1), span_s=Sample.DAY), {3: 90000})
    assert queries.device_range(device, now - timedelta(days=30), now) == {3: 90000}, "> 3 days: daily rows"
    assert queries.device_range(device, day, day + timedelta(days=1)) == {7: 4000}, "short: hourly rows"
    series = queries.stats_series([device], now - timedelta(days=30), now, 'day')
    assert sum(row['es_valid'] for row in series) == 50


def test_retention_checks_the_day_then_deletes_its_hours(device):
    now = timezone.now()
    day = (now - timedelta(days=120)).replace(hour=0, minute=0, second=0, microsecond=0)
    _hour(device, day + timedelta(hours=1), {0: 10000, 5: 4000}, es_valid=10, aircraft_max=5, aircraft_unique=9)
    _hour(device, day + timedelta(hours=7), {0: 6000, 9: 3000}, unit=1000, es_valid=20, aircraft_max=8, aircraft_unique=4)
    _hour(device, now - timedelta(days=2), {1: 2000})        # recent: kept
    out = StringIO()
    call_command('swarm_retention', '--dry-run', stdout=out)
    assert 'would check 1 days (2 hourly samples)' in out.getvalue()
    assert Sample.objects.count() == 3
    call_command('swarm_retention', stdout=StringIO())
    (daily,) = _days(device)
    assert daily.start == day and daily.reports == 2
    assert (daily.es_valid, daily.aircraft_max, daily.aircraft_unique) == (30, 8, 9)
    assert daily.ranges() == {0: 10000, 5: 4000, 9: 4000}, "coarsest unit wins; values round up"
    assert Sample.objects.filter(span_s=Sample.HOUR).count() == 1


def test_a_wrong_or_missing_day_is_fixed_and_counted(device):
    now = timezone.now()
    day = (now - timedelta(days=100)).replace(hour=0, minute=0, second=0, microsecond=0)
    _hour(device, day + timedelta(hours=3), {0: 20000}, es_valid=7)
    Sample.objects.create(device=device, start=day, span_s=Sample.DAY, es_valid=999, reports=5)
    assert retention.roll_up(now)['fixed_days'] == 1
    (daily,) = _days(device)
    assert (daily.es_valid, daily.reports, daily.ranges()) == (7, 1, {0: 20000})


def test_backfill_builds_days_and_deletes_nothing(device):
    now = timezone.now()
    _hour(device, now - timedelta(days=1), {2: 2000}, es_valid=3)
    result = retention.roll_up(now, backfill=True)
    assert result['fixed_days'] == 1 and Sample.objects.filter(span_s=Sample.HOUR).count() == 1
    assert _days(device)[0].es_valid == 3
    assert retention.roll_up(now, backfill=True)['fixed_days'] == 0


@override_settings(ADSBEE_SWARM_HOURLY_RETENTION_DAYS=30, ADSBEE_SWARM_DAILY_RETENTION_DAYS=90)
def test_retention_is_configurable_and_old_days_can_expire(device):
    now = timezone.now()
    _hour(device, now - timedelta(days=40), {0: 2000})
    Sample.objects.create(device=device, start=now - timedelta(days=200), span_s=Sample.DAY)
    result = retention.roll_up(now)
    assert result['expired_days'] == 1
    assert list(Sample.objects.values_list('span_s', flat=True)) == [Sample.DAY]
