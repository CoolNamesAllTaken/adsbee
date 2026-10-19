"""
POST /api/fleet/v1/report: what a bee sends every period (docs/fleet_api.md, "Device report").

401 bad_token, 403 bad_key (the DEVICE_VERIFIER said no), 410 removed, 429 rate_limited
(Retry-After), 400 bad_request. Errors are {"error": code, "detail"?: text}.
"""
from __future__ import annotations

import json
import logging

from django.db import IntegrityError
from django.http import JsonResponse
from django.views.decorators.csrf import csrf_exempt
from django.views.decorators.http import require_POST

from . import conf, protocol, ratelimit, rollout, services
from .models import Device

log = logging.getLogger('adsbee_fleet.report')


def error(status: int, code: str, detail: str = '', retry_after: int | None = None) -> JsonResponse:
    body = {'error': code, **({'detail': detail} if detail else {})}
    response = JsonResponse(body, status=status)
    if retry_after is not None:
        response['Retry-After'] = str(retry_after)
    return response


def client_ip(request) -> str:
    header = conf.get('CLIENT_IP_HEADER')
    if header:
        forwarded = request.headers.get(header, '')
        if forwarded:
            return forwarded.split(',')[0].strip()
    return request.META.get('REMOTE_ADDR', '')


def limited(name: str, ident: str) -> JsonResponse | None:
    wait = ratelimit.hit(name, ident)
    return error(429, 'rate_limited', retry_after=wait) if wait else None


@csrf_exempt
@require_POST
def report(request):
    refused = limited('report_ip', client_ip(request))
    if refused:
        return refused
    header = request.headers.get('Authorization', '')
    account = services.account_by_enroll_token(header[7:].strip()) if header.startswith('Bearer ') else None
    if account is None or not account.has('fleet'):
        return error(401, 'bad_token')
    if len(request.body) > conf.get('MAX_REPORT_BYTES'):
        return error(400, 'bad_request', 'body too large')
    try:
        data = json.loads(request.body or b'null')
        parsed = protocol.parse(data)
    except (ValueError, UnicodeDecodeError) as exc:
        return error(400, 'bad_request', str(exc)[:200])

    verifier = conf.hook('DEVICE_VERIFIER')
    if verifier is not None and not verifier(request, data, account):
        log.info('bad_key account=%s device=%s:%s', account.pk, parsed.product, parsed.unique_id)
        return error(403, 'bad_key')

    try:
        device, _ = Device.objects.get_or_create(account=account, product=parsed.product, unique_id=parsed.unique_id)
    except IntegrityError:      # the same bee's report racing itself
        device = Device.objects.get(account=account, product=parsed.product, unique_id=parsed.unique_id)
    if services.is_turned_away(device):
        return error(410, 'removed')
    refused = limited('report_device', str(device.pk))
    if refused:
        return refused
    protocol.store(device, parsed)
    device.refresh_from_db()
    return JsonResponse({'next_report_s': conf.get('REPORT_PERIOD_S'), 'firmware': rollout.target(device)})
