"""
What a host site calls to run accounts (staff pages, invites) and what the APIs and pages call to
change things. Nothing here checks who is asking: callers do.
"""
from __future__ import annotations

import re
import secrets

from django.contrib.auth import get_user_model
from django.db import transaction
from django.utils import timezone

from . import conf
from .models import Account, ApiToken, Device, Rollout, token_hash


class SwarmError(ValueError):
    """Refused as asked; the message is the sentence to show."""


# ─── Accounts ────────────────────────────────────────────────────────────────

def _check_privileges(privileges) -> list[str]:
    known = conf.get('PRIVILEGES')
    unknown = [p for p in privileges if p not in known]
    if unknown:
        raise SwarmError(f"Unknown privilege: {', '.join(unknown)}")
    return sorted(set(privileges))


@transaction.atomic
def create_account(username: str, *, email: str = '', password: str | None = None,
                   privileges=None) -> tuple[Account, str]:
    """A user and its account. Returns (account, enroll token): the token is shown once.
    No password: the host site sends an invite (set_unusable_password)."""
    User = get_user_model()
    user = User.objects.create_user(username=username, email=email, password=password)
    if password is None:
        user.set_unusable_password()
        user.save()
    account = Account.objects.create(
        user=user, privileges=_check_privileges(conf.get('DEFAULT_PRIVILEGES') if privileges is None else privileges))
    return account, rotate_enroll_token(account)


def account_for(user) -> Account | None:
    if user is None or not user.is_authenticated:
        return None
    return Account.objects.filter(user=user).first()


def set_privileges(account: Account, privileges) -> Account:
    account.privileges = _check_privileges(privileges)
    account.save(update_fields=['privileges'])
    return account


def grant(account: Account, privilege: str) -> Account:
    return set_privileges(account, [*account.privileges, privilege])


def revoke(account: Account, privilege: str) -> Account:
    return set_privileges(account, [p for p in account.privileges if p != privilege])


def set_disabled(account: Account, disabled: bool = True) -> Account:
    """A disabled account's login, API tokens and enroll token stop working; nothing is deleted."""
    account.disabled = disabled
    account.save(update_fields=['disabled'])
    if disabled:
        account.user.is_active = False
    else:
        account.user.is_active = True
    account.user.save(update_fields=['is_active'])
    return account


# ─── Tokens ──────────────────────────────────────────────────────────────────

def rotate_enroll_token(account: Account) -> str:
    """A new enroll token; the old one stops working. 32 hex digits: safe inside AT+SWARM."""
    token = secrets.token_hex(16)
    account.enroll_token_hash = token_hash(token)
    account.enroll_token_prefix = token[:6]
    account.enroll_token_rotated_at = timezone.now()
    account.save(update_fields=['enroll_token_hash', 'enroll_token_prefix', 'enroll_token_rotated_at'])
    return token


def account_by_enroll_token(token: str) -> Account | None:
    if not token or len(token) > 128:
        return None
    account = Account.objects.select_related('user').filter(enroll_token_hash=token_hash(token)).first()
    return account if account is not None and not account.disabled else None


def create_api_token(account: Account, name: str = '') -> tuple[ApiToken, str]:
    token = 'swarm_' + secrets.token_urlsafe(30)
    row = ApiToken.objects.create(account=account, name=name[:64], token_hash=token_hash(token), prefix=token[6:12])
    return row, token


def account_by_api_token(token: str) -> Account | None:
    if not token or len(token) > 128:
        return None
    row = ApiToken.objects.select_related('account__user').filter(token_hash=token_hash(token)).first()
    if row is None or row.account.disabled:
        return None
    ApiToken.objects.filter(pk=row.pk).update(last_used_at=timezone.now())
    return row.account


# ─── Devices ─────────────────────────────────────────────────────────────────

def edit_device(device: Device, data: dict) -> Device:
    """label, note, location ({lat, lon, alt_m} or None to use the reported position)."""
    fields = []
    for key, limit in (('label', 120), ('note', 500)):
        if key in data:
            value = data[key]
            if not isinstance(value, str) or len(value) > limit:
                raise SwarmError(f'{key} must be text up to {limit} characters')
            setattr(device, key, value.strip())
            fields.append(key)
    if 'location' in data:
        location = data['location']
        if location is None:
            device.lat = device.lon = device.alt_m = None
        else:
            device.lat, device.lon, device.alt_m = _location(location)
        fields += ['lat', 'lon', 'alt_m']
    if fields:
        device.save(update_fields=fields)
    return device


def _location(value) -> tuple[float, float, float | None]:
    try:
        lat, lon = float(value['lat']), float(value['lon'])
        alt = value.get('alt_m')
        alt = None if alt in (None, '') else float(alt)
    except (TypeError, KeyError, ValueError) as exc:
        raise SwarmError('location needs numbers lat and lon (alt_m optional)') from exc
    if not (-90 <= lat <= 90 and -180 <= lon <= 180):
        raise SwarmError('location is off the map')
    return lat, lon, alt


def remove_device(device: Device) -> Device:
    """Off the account: its reports answer 410 until the enroll token is rotated or it is restored."""
    device.removed_at = timezone.now()
    device.save(update_fields=['removed_at'])
    return device


def restore_device(device: Device) -> Device:
    device.removed_at = None
    device.save(update_fields=['removed_at'])
    return device


def is_turned_away(device: Device) -> bool:
    """Removed, and the enroll token has not changed since."""
    if device.removed_at is None:
        return False
    rotated = device.account.enroll_token_rotated_at
    if rotated is not None and rotated > device.removed_at:
        restore_device(device)
        return False
    return True


# ─── Rollouts ────────────────────────────────────────────────────────────────

TAG = re.compile(r'^[0-9A-Za-z._+-]{1,64}$')


def _owned(account: Account, ids) -> list[Device]:
    ids = list(ids or [])
    if not all(isinstance(i, int) for i in ids):
        raise SwarmError('devices are given by id')
    found = list(Device.objects.filter(account=account, pk__in=ids, removed_at__isnull=True))
    if len(found) != len(set(ids)):
        raise SwarmError('Not every device is on this account')
    return found


@transaction.atomic
def create_rollout(account: Account, data: dict) -> Rollout:
    """product, tag, channel?, scope (all|label|devices), label?, devices?, test_devices?, note?
    With test_devices the rollout starts in stage `test`; `promote` widens it to the scope."""
    product = data.get('product')
    if product not in conf.products():
        raise SwarmError('Unknown product')
    tag = str(data.get('tag') or '').strip()
    if not TAG.match(tag):
        raise SwarmError('tag must be a version tag like 0.9.2')
    validator = conf.hook('TAG_VALIDATOR')
    problem = validator(product, tag) if validator else None
    if problem:
        raise SwarmError(problem)
    channel = str(data.get('channel') or ('rc' if '-rc' in tag.lower() else 'stable'))[:16]
    scope = data.get('scope', Rollout.SCOPE_ALL)
    if scope not in dict(Rollout.SCOPES):
        raise SwarmError('scope is all, label or devices')
    label = str(data.get('label') or '').strip()
    if scope == Rollout.SCOPE_LABEL and not label:
        raise SwarmError('Give the label')
    devices = _owned(account, data.get('devices'))
    if scope == Rollout.SCOPE_DEVICES and not devices:
        raise SwarmError('Choose the bees')
    tests = _owned(account, data.get('test_devices'))
    rollout = Rollout.objects.create(
        account=account, product=product, tag=tag, channel=channel, scope=scope, label=label[:120],
        stage=Rollout.STAGE_TEST if tests else Rollout.STAGE_ALL, note=str(data.get('note') or '')[:200])
    rollout.devices.set(devices)
    rollout.test_devices.set(tests)
    return rollout


def rollout_action(rollout: Rollout, action: str) -> Rollout:
    """promote (test bees -> every bee in scope), pause, resume, cancel."""
    if rollout.cancelled_at:
        raise SwarmError('This rollout was cancelled')
    if action == 'promote':
        rollout.stage, rollout.promoted_at = Rollout.STAGE_ALL, timezone.now()
    elif action == 'pause':
        rollout.paused = True
    elif action == 'resume':
        rollout.paused = False
    elif action == 'cancel':
        rollout.cancelled_at = timezone.now()
    else:
        raise SwarmError('action is promote, pause, resume or cancel')
    rollout.save()
    return rollout
