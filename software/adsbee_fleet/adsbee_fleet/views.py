"""
The reference UI: plain server-rendered pages so a self-hosted server is usable as it comes.
Host sites with their own look include only `adsbee_fleet.api_urls` and build on the API.
"""
from __future__ import annotations

import math
from datetime import timedelta
from functools import wraps

from django.contrib import messages
from django.contrib.auth.decorators import login_required
from django.http import HttpResponseForbidden
from django.shortcuts import get_object_or_404, redirect, render
from django.utils import timezone
from django.views.decorators.http import require_POST

from . import conf, queries, ranges, rollout as rollouts, services
from .api_user import device_json
from .models import Device, Rollout

WINDOWS = {'24h': timedelta(hours=24), '7d': timedelta(days=7), '30d': timedelta(days=30), '1y': timedelta(days=365)}


def fleet_page(func):
    @login_required
    @wraps(func)
    def inner(request, *args, **kwargs):
        account = services.account_for(request.user)
        if account is None or not account.has('fleet'):
            return HttpResponseForbidden('This login has no fleet.')
        request.account = account
        return func(request, *args, **kwargs)
    return inner


def _window(request) -> tuple[str, timezone.datetime, timezone.datetime]:
    key = request.GET.get('w') if request.GET.get('w') in WINDOWS else '7d'
    until = timezone.now()
    return key, until - WINDOWS[key], until


@fleet_page
def device_list(request):
    devices = list(request.account.devices.filter(removed_at__isnull=True))
    key, since, until = _window(request)
    reach = {d['id']: d['max_range_m'] for d in queries.fleet_range(devices, since, until)['devices']}
    rows = [{**device_json(d), 'max_range_m': reach.get(d.pk)} for d in devices]
    removed = request.account.devices.filter(removed_at__isnull=False)
    return render(request, 'adsbee_fleet/devices.html', {
        'rows': rows, 'removed': removed, 'window': key, 'windows': WINDOWS,
        'markers': [{'id': r['id'], 'label': r['label'] or r['unique_id'], 'lat': r['position']['lat'],
                     'lon': r['position']['lon'], 'range_m': r['max_range_m']} for r in rows if r['position']],
        'stale_before': timezone.now() - timedelta(hours=3)})


@fleet_page
def device_detail(request, pk: int):
    device = get_object_or_404(Device, pk=pk, account=request.account)
    if request.method == 'POST':
        action = request.POST.get('action')
        try:
            if action == 'save':
                location = None
                if request.POST.get('lat') or request.POST.get('lon'):
                    location = {'lat': request.POST.get('lat'), 'lon': request.POST.get('lon'),
                                'alt_m': request.POST.get('alt_m')}
                services.edit_device(device, {'label': request.POST.get('label', ''),
                                              'note': request.POST.get('note', ''), 'location': location})
            elif action == 'remove':
                services.remove_device(device)
                return redirect('adsbee_fleet:devices')
            elif action == 'restore':
                services.restore_device(device)
        except services.FleetError as exc:
            messages.error(request, str(exc))
        return redirect('adsbee_fleet:device', pk=device.pk)
    key, since, until = _window(request)
    merged = queries.device_range(device, since, until)
    scale = max(merged.values(), default=0)
    plots = [{'title': _band_title(band), 'svg': polar_svg(_band(merged, band), scale)} for band in range(ranges.BANDS)]
    return render(request, 'adsbee_fleet/device.html', {
        'device': device, 'info': device_json(device), 'window': key, 'windows': WINDOWS,
        'overall': polar_svg(ranges.sector_max(merged), scale, size=320), 'plots': plots,
        'max_km': round(scale / 1000) if scale else None,
        'stats': queries.stats_series([device], since, until, 'hour' if key in ('24h', '7d') else 'day'),
        'target': rollouts.target(device)})


def _band(merged: ranges.Map, band: int) -> list[int | None]:
    return [merged.get(ranges.bin_index(band, sector)) for sector in range(ranges.SECTORS)]


def _band_title(band: int) -> str:
    low, high = ranges.band_edges_ft()[band]
    return f"{low // 1000}–{high // 1000}k ft" if high else f"≥{low // 1000}k ft"


def polar_svg(values: list[int | None], scale: int, size: int = 140) -> str:
    """36 wedges, north up, radius = range / scale; rings every 50 km (or a quarter of the scale)."""
    half = size / 2
    radius = half - 4
    parts = [f'<svg viewBox="0 0 {size} {size}" width="{size}" height="{size}" class="polar" role="img">',
             f'<circle cx="{half}" cy="{half}" r="{radius}" class="ring"/>']
    if scale:
        step = 50000 if scale > 100000 else max(scale / 4, 1)
        ring = step
        while ring < scale:
            parts.append(f'<circle cx="{half}" cy="{half}" r="{radius * ring / scale:.1f}" class="ring">'
                         f'<title>{ring / 1000:.0f} km</title></circle>')
            ring += step
    parts.append(f'<line x1="{half}" y1="2" x2="{half}" y2="{size - 2}" class="axis"/>'
                 f'<line x1="2" y1="{half}" x2="{size - 2}" y2="{half}" class="axis"/>')
    for sector, meters in enumerate(values):
        if not meters or not scale:
            continue
        r = radius * meters / scale
        a0, a1 = math.radians(sector * ranges.SECTOR_DEG), math.radians((sector + 1) * ranges.SECTOR_DEG)
        x0, y0 = half + r * math.sin(a0), half - r * math.cos(a0)
        x1, y1 = half + r * math.sin(a1), half - r * math.cos(a1)
        parts.append(f'<path d="M{half},{half} L{x0:.1f},{y0:.1f} A{r:.1f},{r:.1f} 0 0 1 {x1:.1f},{y1:.1f} Z" '
                     f'class="wedge"><title>{sector * 10}–{sector * 10 + 10}°: {meters / 1000:.0f} km</title></path>')
    parts.append(f'<text x="{half}" y="11" class="north">N</text></svg>')
    return ''.join(parts)


@fleet_page
def rollout_page(request):
    account = request.account
    if request.method == 'POST':
        try:
            if request.POST.get('action') == 'create':
                services.create_rollout(account, {
                    'product': request.POST.get('product'), 'tag': request.POST.get('tag'),
                    'scope': request.POST.get('scope'), 'label': request.POST.get('label'),
                    'devices': [int(i) for i in request.POST.getlist('devices')],
                    'test_devices': [int(i) for i in request.POST.getlist('test_devices')],
                    'note': request.POST.get('note', '')})
            else:
                services.rollout_action(get_object_or_404(Rollout, pk=request.POST.get('rollout'), account=account),
                                        request.POST.get('action', ''))
        except (services.FleetError, ValueError) as exc:
            messages.error(request, str(exc))
        return redirect('adsbee_fleet:rollouts')
    return render(request, 'adsbee_fleet/rollouts.html', {
        'rollouts': [{'r': r, 'progress': rollouts.progress(r)} for r in account.rollouts.all()[:50]],
        'devices': account.devices.filter(removed_at__isnull=True),
        'labels': sorted({d.label for d in account.devices.all() if d.label}),
        'products': conf.products(), 'scopes': Rollout.SCOPES})


@fleet_page
def account_page(request):
    return render(request, 'adsbee_fleet/account.html', {
        'account': request.account, 'tokens': request.account.api_tokens.order_by('-created_at'),
        'base': request.build_absolute_uri('/').rstrip('/')})


@fleet_page
@require_POST
def account_action(request):
    action = request.POST.get('action')
    context = {'account': request.account, 'base': request.build_absolute_uri('/').rstrip('/')}
    if action == 'rotate':
        context['enroll_token'] = services.rotate_enroll_token(request.account)
    elif action == 'api_token':
        context['api_token'] = services.create_api_token(request.account, request.POST.get('name', ''))[1]
    elif action == 'delete_token':
        request.account.api_tokens.filter(pk=request.POST.get('token')).delete()
        return redirect('adsbee_fleet:account')
    context['tokens'] = request.account.api_tokens.order_by('-created_at')
    return render(request, 'adsbee_fleet/account.html', context)
