"""
The device report, v1 (docs/fleet_api.md): validated into a `Report`, then stored by `ingest`.

Retries (the device keeps seq and period.start_uptime_s until a report is acknowledged):
same seq, start and len_s is a duplicate and is not stored; same seq and start with a longer len_s
is the earlier report widened, so it replaces that report's stats and max-merges its range.
"""
from __future__ import annotations

import math
import re
from dataclasses import dataclass, field
from datetime import datetime, timedelta

from django.db import transaction
from django.utils import timezone

from . import conf, ranges
from .models import PEAK_STATS, STATS, Device, Sample

UNIQUE_ID = re.compile(r'^[0-9A-F]{16}$')
MAC = re.compile(r'^[0-9A-F]{2}(:[0-9A-F]{2}){5}$')
VERSION = re.compile(r'^[0-9A-Za-z._+-]{0,64}$')
SOURCE = re.compile(r'^[a-z0-9_]{0,16}$')
MAX_COUNT = 2 ** 40


class ReportError(ValueError):
    """400 bad_request; the message is the detail."""


@dataclass
class Report:
    product: str
    unique_id: str
    mac_address: str
    versions: dict
    auto_update: bool
    uptime_s: int
    seq: int
    start_uptime_s: int
    len_s: int
    rx_position: dict | None
    stats: dict
    unit_m: int = ranges.DEFAULT_UNIT_M
    ranges: ranges.Map = field(default_factory=dict)


def _int(data: dict, key: str, low: int = 0, high: int = MAX_COUNT) -> int:
    value = data.get(key)
    if isinstance(value, bool) or not isinstance(value, int) or not low <= value <= high:
        raise ReportError(f'{key} must be an integer {low}..{high}')
    return value


def _number(data: dict, key: str, low: float, high: float) -> float:
    value = data.get(key)
    if isinstance(value, bool) or not isinstance(value, (int, float)) or not math.isfinite(value) \
            or not low <= value <= high:
        raise ReportError(f'rx_position.{key} must be a number {low}..{high}')
    return float(value)


def parse(data) -> Report:
    if not isinstance(data, dict):
        raise ReportError('body must be a JSON object')
    if data.get('v') != 1:
        raise ReportError('v must be 1')
    product = data.get('product')
    if product not in conf.products():
        raise ReportError('unknown product')
    unique_id = str(data.get('unique_id') or '').strip().upper()
    if not UNIQUE_ID.match(unique_id):
        raise ReportError('unique_id must be 16 hex digits')
    mac = str(data.get('mac_address') or '').strip().upper().replace('-', ':')
    if mac and not MAC.match(mac):
        raise ReportError('mac_address must look like DC:54:75:D2:6C:24')
    versions = data.get('versions') or {}
    if (not isinstance(versions, dict) or len(versions) > 8
            or not all(isinstance(k, str) and len(k) <= 16 and isinstance(v, str) and VERSION.match(v)
                       for k, v in versions.items())):
        raise ReportError('versions must map component to version string')
    auto_update = data.get('auto_update', False)
    if not isinstance(auto_update, bool):
        raise ReportError('auto_update must be true or false')
    period = data.get('period')
    if not isinstance(period, dict):
        raise ReportError('period must be an object')
    stats = data.get('stats') or {}
    if not isinstance(stats, dict):
        raise ReportError('stats must be an object')
    report = Report(
        product=product, unique_id=unique_id, mac_address=mac, versions=versions, auto_update=auto_update,
        uptime_s=_int(data, 'uptime_s'), seq=_int(data, 'seq'),
        start_uptime_s=_int(period, 'start_uptime_s'), len_s=_int(period, 'len_s', 1, 7 * 86400),
        rx_position=_position(data.get('rx_position')),
        stats={key: _int(stats, key) if key in stats else 0 for key in STATS})
    if data.get('range') is not None and report.rx_position is not None:
        report.unit_m, report.ranges = _range(data['range'])
    return report


def _position(value) -> dict | None:
    if value is None:
        return None
    if not isinstance(value, dict):
        raise ReportError('rx_position must be an object or null')
    source = str(value.get('source') or '')[:16]
    if not SOURCE.match(source):
        raise ReportError('rx_position.source must be a short lowercase word')
    alt = value.get('alt_m')
    return {'lat': _number(value, 'lat', -90, 90), 'lon': _number(value, 'lon', -180, 180),
            'alt_m': None if alt is None else _number(value, 'alt_m', -1000, 100000), 'source': source}


def _range(value) -> tuple[int, ranges.Map]:
    if not isinstance(value, dict):
        raise ReportError('range must be an object')
    if value.get('sectors') != ranges.SECTORS or value.get('bands') != ranges.BANDS:
        raise ReportError(f'range must be {ranges.SECTORS} sectors x {ranges.BANDS} bands')
    unit = _int(value, 'unit_m', 1, 1_000_000)
    try:
        return unit, ranges.decode(value.get('changed'), value.get('max'), unit)
    except ranges.RangeError as exc:
        raise ReportError(str(exc)) from exc


def hour_of(moment: datetime) -> datetime:
    return moment.replace(minute=0, second=0, microsecond=0)


def ingest(device: Device, report: Report, now: datetime | None = None) -> bool:
    """Store a report on `device` (locked by the caller). Returns False for a duplicate."""
    now = now or timezone.now()
    key = [report.seq, report.start_uptime_s, report.len_s]
    last = device.last_report or {}
    previous = last.get('key') or [None, None, None]
    widened = previous[:2] == key[:2] and previous[2] is not None and report.len_s > previous[2]
    if previous == key or (previous[:2] == key[:2] and not widened):
        return False

    if widened:
        sample = Sample.objects.select_for_update().filter(
            device=device, span_s=Sample.HOUR, start=last['start']).first()
    else:
        sample = None
    if sample is None:
        sample, _ = Sample.objects.select_for_update().get_or_create(
            device=device, span_s=Sample.HOUR, start=hour_of(now))
        replaced = {}
    else:
        replaced = last.get('stats') or {}
    for name in STATS:
        if name in PEAK_STATS:
            setattr(sample, name, max(getattr(sample, name), report.stats[name]))
        else:
            setattr(sample, name, max(0, getattr(sample, name) - replaced.get(name, 0)) + report.stats[name])
    if not replaced:
        sample.reports += 1
    if report.ranges:
        merged = ranges.merge(sample.ranges(), report.ranges)
        sample.unit_m = max(sample.unit_m if sample.range_map else 0, report.unit_m)
        sample.set_ranges(merged)
    sample.save()

    device.mac_address = report.mac_address or device.mac_address
    device.versions = report.versions
    device.auto_update = report.auto_update
    device.uptime_s = report.uptime_s
    device.last_report_at = now
    if report.rx_position is not None:
        device.rx_lat, device.rx_lon = report.rx_position['lat'], report.rx_position['lon']
        device.rx_alt_m, device.rx_source = report.rx_position['alt_m'], report.rx_position['source']
    device.last_report = {'key': key, 'start': sample.start.isoformat(), 'stats': report.stats}
    device.save()
    return True


def store(device: Device, report: Report, now: datetime | None = None) -> bool:
    """Ingest under a row lock on the device. Returns False for a duplicate."""
    with transaction.atomic():
        device = Device.objects.select_for_update().get(pk=device.pk)
        return ingest(device, report, now)


def window(since: datetime | None, until: datetime | None, default_days: int = 7) -> tuple[datetime, datetime]:
    until = until or timezone.now()
    return since or until - timedelta(days=default_days), until
