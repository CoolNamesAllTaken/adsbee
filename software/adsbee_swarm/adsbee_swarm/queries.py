"""The read side: range maps and stats over a time window, for one bee or an account's swarm."""
from __future__ import annotations

from collections import defaultdict
from datetime import datetime, timedelta, timezone as tz


from . import ranges
from .models import PEAK_STATS, STATS, Device, Sample


#: Windows longer than this read daily rows (kept from the first report); shorter ones hourly.
DAILY_AFTER = timedelta(days=3)


def _samples(devices, since: datetime, until: datetime, span: int | None = None):
    """Hourly rows starting inside the window, or daily rows whose day overlaps it."""
    span = span or (Sample.DAY if until - since > DAILY_AFTER else Sample.HOUR)
    rows = Sample.objects.filter(device__in=devices, span_s=span, start__lt=until)
    rows = rows.filter(start__gte=since) if span == Sample.HOUR else rows.filter(start__gt=since - timedelta(days=1))
    return rows.order_by('start')


def device_range(device: Device, since: datetime, until: datetime) -> ranges.Map:
    merged: ranges.Map = {}
    for sample in _samples([device], since, until).only('range_map', 'unit_m').exclude(range_map=None):
        ranges.merge(merged, sample.ranges())
    return merged


def range_payload(device: Device, merged: ranges.Map) -> dict:
    return {'id': device.pk, 'label': device.label, 'unique_id': device.unique_id,
            'position': device.position, 'max_m': ranges.matrix(merged),
            'sector_max_m': ranges.sector_max(merged), 'bins': len(merged),
            'max_range_m': max(merged.values(), default=None)}


def swarm_range(devices, since: datetime, until: datetime) -> dict:
    """Per bee its bands x sectors maxima; `swarm` is the max per bin over all of them."""
    per_device = []
    swarm: ranges.Map = {}
    for device in devices:
        merged = device_range(device, since, until)
        ranges.merge(swarm, merged)
        per_device.append(range_payload(device, merged))
    return {'since': since.isoformat(), 'until': until.isoformat(),
            'sectors': ranges.SECTORS, 'bands': ranges.BANDS, 'sector_deg': ranges.SECTOR_DEG,
            'band_edges_ft': ranges.band_edges_ft(), 'devices': per_device,
            'swarm': {'max_m': ranges.matrix(swarm), 'sector_max_m': ranges.sector_max(swarm)}}


def stats_series(devices, since: datetime, until: datetime, step: str = 'hour') -> list[dict]:
    """Counts summed over bees per step; peaks (aircraft_max, aircraft_unique) are summed too
    across bees (each bee hears its own sky), maxed within a bee's step."""
    width = 3600 if step == 'hour' else 86400
    per_bee: dict = defaultdict(lambda: defaultdict(int))
    span = Sample.HOUR if step == 'hour' else Sample.DAY
    for sample in _samples(devices, since, until, span).values('device_id', 'start', *STATS):
        epoch = int(sample['start'].timestamp()) // width * width
        slot = per_bee[(epoch, sample['device_id'])]
        for name in STATS:
            slot[name] = max(slot[name], sample[name]) if name in PEAK_STATS else slot[name] + sample[name]
    totals: dict = defaultdict(lambda: dict.fromkeys(STATS, 0))
    for (epoch, _device), slot in per_bee.items():
        for name in STATS:
            totals[epoch][name] += slot[name]
    return [{'t': datetime.fromtimestamp(epoch, tz.utc).isoformat(), **totals[epoch]} for epoch in sorted(totals)]
