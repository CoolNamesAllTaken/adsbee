"""
    User ── Account ──< ApiToken             one login per account; privileges are flags
               └──< Device ──< Sample        hourly (later daily) stats + range map
               └──< Rollout >──< Device      a firmware target for all, a label, or chosen bees

An account's enroll token (what a bee is given with AT+SWARM) and its API tokens are stored as
SHA-256 hashes; the plain token is shown once.
"""
from __future__ import annotations

import hashlib

from django.conf import settings
from django.db import models
from django.utils import timezone

from . import ranges


def token_hash(token: str) -> str:
    return hashlib.sha256(token.encode()).hexdigest()


class Account(models.Model):
    user = models.OneToOneField(settings.AUTH_USER_MODEL, on_delete=models.CASCADE, related_name='swarm_account')
    #: Privilege flags (conf PRIVILEGES): ["swarm", "wiggler", ...].
    privileges = models.JSONField(default=list, blank=True)
    disabled = models.BooleanField(default=False)
    enroll_token_hash = models.CharField(max_length=64, unique=True, null=True, blank=True)
    #: The first characters, so a person can tell which token a bee holds.
    enroll_token_prefix = models.CharField(max_length=8, blank=True)
    enroll_token_rotated_at = models.DateTimeField(null=True, blank=True)
    created_at = models.DateTimeField(default=timezone.now)

    def __str__(self):
        return self.user.get_username()

    def has(self, privilege: str) -> bool:
        return not self.disabled and privilege in (self.privileges or [])


class ApiToken(models.Model):
    account = models.ForeignKey(Account, on_delete=models.CASCADE, related_name='api_tokens')
    name = models.CharField(max_length=64, blank=True)
    token_hash = models.CharField(max_length=64, unique=True)
    prefix = models.CharField(max_length=8)
    created_at = models.DateTimeField(default=timezone.now)
    last_used_at = models.DateTimeField(null=True, blank=True)

    def __str__(self):
        return f'{self.prefix}… {self.name}'


class Device(models.Model):
    account = models.ForeignKey(Account, on_delete=models.CASCADE, related_name='devices')
    product = models.CharField(max_length=32)
    #: RP2040 flash UID (1090), 16 uppercase hex digits.
    unique_id = models.CharField(max_length=16)
    mac_address = models.CharField(max_length=17, blank=True)
    label = models.CharField(max_length=120, blank=True)
    note = models.CharField(max_length=500, blank=True)
    #: Set by the owner: where the map shows the bee. Empty: `rx_*` as reported.
    lat = models.FloatField(null=True, blank=True)
    lon = models.FloatField(null=True, blank=True)
    alt_m = models.FloatField(null=True, blank=True)
    rx_lat = models.FloatField(null=True, blank=True)
    rx_lon = models.FloatField(null=True, blank=True)
    rx_alt_m = models.FloatField(null=True, blank=True)
    rx_source = models.CharField(max_length=16, blank=True)
    versions = models.JSONField(default=dict, blank=True)
    auto_update = models.BooleanField(default=False)
    uptime_s = models.BigIntegerField(null=True, blank=True)
    first_seen = models.DateTimeField(default=timezone.now)
    last_report_at = models.DateTimeField(null=True, blank=True)
    #: Removed by the owner: reports answer 410 until the enroll token is rotated or it is restored.
    removed_at = models.DateTimeField(null=True, blank=True)
    #: The last report stored: [seq, start_uptime_s, len_s], its Sample's start and its stats, so a
    #: retry is recognized and a merged retry replaces what it widens.
    last_report = models.JSONField(default=dict, blank=True)

    class Meta:
        ordering = ['label', 'unique_id']
        constraints = [models.UniqueConstraint(fields=['account', 'product', 'unique_id'], name='swarm_device_unique')]

    def __str__(self):
        return self.label or f'{self.product}:{self.unique_id}'

    @property
    def removed(self) -> bool:
        return self.removed_at is not None

    @property
    def position(self) -> dict | None:
        """Where to draw the bee: the owner's location, else the reported one."""
        if self.lat is not None and self.lon is not None:
            return {'lat': self.lat, 'lon': self.lon, 'alt_m': self.alt_m, 'source': 'owner'}
        if self.rx_lat is not None and self.rx_lon is not None:
            return {'lat': self.rx_lat, 'lon': self.rx_lon, 'alt_m': self.rx_alt_m, 'source': self.rx_source}
        return None

    @property
    def version(self) -> str:
        from . import conf

        key = conf.products().get(self.product, {}).get('version_key', '')
        return str((self.versions or {}).get(key, ''))


STATS = ('modes_valid', 'es_valid', 'uat_adsb', 'uat_uplink', 'aircraft_max', 'aircraft_unique')
#: Stats that are a peak, not a count: merged by max rather than summed.
PEAK_STATS = ('aircraft_max', 'aircraft_unique')


class Sample(models.Model):
    """One device's hour (span 3600) or, after retention, day (86400): summed counts, max range."""
    HOUR, DAY = 3600, 86400
    device = models.ForeignKey(Device, on_delete=models.CASCADE, related_name='samples')
    start = models.DateTimeField()
    span_s = models.PositiveIntegerField(default=HOUR)
    reports = models.PositiveIntegerField(default=0)
    modes_valid = models.BigIntegerField(default=0)
    es_valid = models.BigIntegerField(default=0)
    uat_adsb = models.BigIntegerField(default=0)
    uat_uplink = models.BigIntegerField(default=0)
    aircraft_max = models.IntegerField(default=0)
    aircraft_unique = models.IntegerField(default=0)
    unit_m = models.PositiveIntegerField(default=ranges.DEFAULT_UNIT_M)
    #: `ranges.pack`: 54-byte bitmap, then one byte per present bin.
    range_map = models.BinaryField(null=True, blank=True)

    class Meta:
        ordering = ['start']
        constraints = [models.UniqueConstraint(fields=['device', 'start', 'span_s'], name='swarm_sample_unique')]
        indexes = [models.Index(fields=['device', 'span_s', 'start'])]

    def ranges(self) -> ranges.Map:
        return ranges.unpack(self.range_map, self.unit_m)

    def set_ranges(self, values: ranges.Map) -> None:
        """Store `values`, coarsening to the largest unit any of them came in."""
        self.range_map = ranges.pack(values, self.unit_m) if values else None


class Rollout(models.Model):
    """
    A firmware target for an account's bees of one product. Scope picks the bees; a rollout in
    stage `test` targets only its test bees, `all` every bee in scope. Newest active rollout wins.
    """
    SCOPE_ALL, SCOPE_LABEL, SCOPE_DEVICES = 'all', 'label', 'devices'
    SCOPES = [(SCOPE_ALL, 'All bees'), (SCOPE_LABEL, 'Bees with a label'), (SCOPE_DEVICES, 'Chosen bees')]
    STAGE_TEST, STAGE_ALL = 'test', 'all'
    STAGES = [(STAGE_TEST, 'Test bees'), (STAGE_ALL, 'Every bee in scope')]
    account = models.ForeignKey(Account, on_delete=models.CASCADE, related_name='rollouts')
    product = models.CharField(max_length=32)
    tag = models.CharField(max_length=64)
    channel = models.CharField(max_length=16, default='stable')
    scope = models.CharField(max_length=8, choices=SCOPES, default=SCOPE_ALL)
    label = models.CharField(max_length=120, blank=True)
    devices = models.ManyToManyField(Device, blank=True, related_name='rollouts')
    test_devices = models.ManyToManyField(Device, blank=True, related_name='test_rollouts')
    stage = models.CharField(max_length=8, choices=STAGES, default=STAGE_ALL)
    paused = models.BooleanField(default=False)
    cancelled_at = models.DateTimeField(null=True, blank=True)
    note = models.CharField(max_length=200, blank=True)
    created_at = models.DateTimeField(default=timezone.now)
    promoted_at = models.DateTimeField(null=True, blank=True)

    class Meta:
        ordering = ['-created_at', '-id']

    def __str__(self):
        return f'{self.product} {self.tag} #{self.pk}'

    @property
    def state(self) -> str:
        if self.cancelled_at:
            return 'cancelled'
        if self.paused:
            return 'paused'
        return self.stage
