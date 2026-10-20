"""
Which firmware a bee is told about: the report response's `firmware` field.

The newest rollout of the bee's account and product that is not cancelled and includes the bee.
A paused one still decides (newer rollouts win, older ones do not take over) but offers nothing.
The bee installs it only with its own AT+AUTO_UPDATE=1.
"""
from __future__ import annotations

from .models import Device, Rollout


def includes(rollout: Rollout, device: Device) -> bool:
    if device.product != rollout.product or device.removed_at is not None:
        return False
    if rollout.stage == Rollout.STAGE_TEST:
        return rollout.test_devices.filter(pk=device.pk).exists()
    if rollout.test_devices.filter(pk=device.pk).exists():
        return True
    if rollout.scope == Rollout.SCOPE_LABEL:
        return device.label == rollout.label
    if rollout.scope == Rollout.SCOPE_DEVICES:
        return rollout.devices.filter(pk=device.pk).exists()
    return True


def deciding(device: Device) -> Rollout | None:
    for rollout in (Rollout.objects.filter(account_id=device.account_id, product=device.product,
                                           cancelled_at__isnull=True).order_by('-created_at', '-id')):
        if includes(rollout, device):
            return rollout
    return None


def target(device: Device) -> dict | None:
    rollout = deciding(device)
    if rollout is None or rollout.paused:
        return None
    return {'tag': rollout.tag, 'channel': rollout.channel}


def progress(rollout: Rollout) -> dict:
    """Bees this rollout decides for, and how many report its tag."""
    bees = [d for d in rollout.account.devices.filter(product=rollout.product, removed_at__isnull=True)
            if deciding(d) == rollout]
    return {'targeted': len(bees), 'on_tag': sum(1 for d in bees if d.version == rollout.tag),
            'auto_update': sum(1 for d in bees if d.auto_update)}
