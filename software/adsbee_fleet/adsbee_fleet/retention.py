"""
Hourly samples older than HOURLY_RETENTION_DAYS become one daily sample per bee and day (counts
summed, peaks and range maxed); daily ones older than DAILY_RETENTION_DAYS (if set) are deleted.
Run daily: `manage.py fleet_retention`. Idempotent: a day already rolled up absorbs late hours.
"""
from __future__ import annotations

from collections import defaultdict
from datetime import datetime, timedelta

from django.db import transaction
from django.utils import timezone

from . import conf, ranges
from .models import PEAK_STATS, STATS, Sample


def _day(moment: datetime) -> datetime:
    return moment.replace(hour=0, minute=0, second=0, microsecond=0)


def roll_up(now: datetime | None = None, *, dry_run: bool = False) -> dict:
    now = now or timezone.now()
    # Whole days only, so a day is rolled up once its last hour has aged out.
    cutoff = _day(now - timedelta(days=conf.get('HOURLY_RETENTION_DAYS')))
    hourly = Sample.objects.filter(span_s=Sample.HOUR, start__lt=cutoff)
    groups: dict = defaultdict(list)
    for sample in hourly.order_by('device_id', 'start').iterator():
        groups[(sample.device_id, _day(sample.start))].append(sample)
    days = conf.get('DAILY_RETENTION_DAYS')
    expired = Sample.objects.filter(span_s=Sample.DAY, start__lt=_day(now - timedelta(days=days))) if days else None
    result = {'hours': sum(len(g) for g in groups.values()), 'days': len(groups),
              'expired_days': expired.count() if expired is not None else 0}
    if dry_run:
        return result
    for (device_id, day), samples in groups.items():
        with transaction.atomic():
            daily, _ = Sample.objects.select_for_update().get_or_create(device_id=device_id, start=day,
                                                                       span_s=Sample.DAY)
            merged = daily.ranges()
            unit = daily.unit_m if daily.range_map else 0
            for sample in samples:
                daily.reports += sample.reports
                for name in STATS:
                    value = getattr(sample, name)
                    setattr(daily, name, max(getattr(daily, name), value) if name in PEAK_STATS
                            else getattr(daily, name) + value)
                if sample.range_map:
                    ranges.merge(merged, sample.ranges())
                    unit = max(unit, sample.unit_m)
            if merged:
                daily.unit_m = unit
                daily.set_ranges(merged)
            daily.save()
            Sample.objects.filter(pk__in=[s.pk for s in samples]).delete()
    if expired is not None:
        expired.delete()
    return result
