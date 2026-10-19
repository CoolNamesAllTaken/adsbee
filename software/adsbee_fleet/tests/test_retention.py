from datetime import timedelta
from io import StringIO

import pytest
from django.core.management import call_command
from django.test import override_settings
from django.utils import timezone

from adsbee_fleet import retention
from adsbee_fleet.models import Device, Sample

pytestmark = pytest.mark.django_db


@pytest.fixture
def device(owner):
    return Device.objects.create(account=owner.account, product='adsbee_1090', unique_id='E6614C311B5B6F2A')


def _hour(device, start, values, unit=2000, **stats):
    sample = Sample(device=device, start=start, unit_m=unit, reports=1, **stats)
    sample.set_ranges(values)
    sample.save()


def test_old_hours_become_one_day(device):
    now = timezone.now()
    day = (now - timedelta(days=400)).replace(hour=0, minute=0, second=0, microsecond=0)
    _hour(device, day + timedelta(hours=1), {0: 10000, 5: 4000}, es_valid=10, aircraft_max=5, aircraft_unique=9)
    _hour(device, day + timedelta(hours=7), {0: 6000, 9: 3000}, unit=1000, es_valid=20, aircraft_max=8, aircraft_unique=4)
    _hour(device, now - timedelta(days=2), {1: 2000})        # recent: untouched
    out = StringIO()
    call_command('fleet_retention', '--dry-run', stdout=out)
    assert 'would roll 2 hourly samples into 1 days' in out.getvalue()
    assert Sample.objects.count() == 3
    call_command('fleet_retention', stdout=StringIO())
    daily = Sample.objects.get(span_s=Sample.DAY)
    assert daily.start == day and daily.reports == 2
    assert (daily.es_valid, daily.aircraft_max, daily.aircraft_unique) == (30, 8, 9)
    assert daily.ranges() == {0: 10000, 5: 4000, 9: 4000}, "coarsest unit wins; values round up"
    assert Sample.objects.filter(span_s=Sample.HOUR).count() == 1


def test_a_late_hour_joins_its_rolled_up_day(device):
    now = timezone.now()
    day = (now - timedelta(days=400)).replace(hour=0, minute=0, second=0, microsecond=0)
    _hour(device, day, {0: 10000}, es_valid=1)
    retention.roll_up(now)
    _hour(device, day + timedelta(hours=5), {0: 20000}, es_valid=2)
    retention.roll_up(now)
    daily = Sample.objects.get()
    assert daily.span_s == Sample.DAY and daily.es_valid == 3 and daily.ranges() == {0: 20000}


@override_settings(ADSBEE_FLEET_HOURLY_RETENTION_DAYS=30, ADSBEE_FLEET_DAILY_RETENTION_DAYS=90)
def test_retention_is_configurable_and_old_days_expire(device):
    now = timezone.now()
    _hour(device, now - timedelta(days=40), {0: 2000})
    Sample.objects.create(device=device, start=now - timedelta(days=200), span_s=Sample.DAY)
    result = retention.roll_up(now)
    assert result['expired_days'] == 1
    assert list(Sample.objects.values_list('span_s', flat=True)) == [Sample.DAY]
