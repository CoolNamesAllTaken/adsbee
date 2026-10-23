from __future__ import annotations

import json
import random

import pytest
from django.core.cache import cache

from adsbee_swarm import services
from adsbee_swarm.simulator import Bee


@pytest.fixture(autouse=True)
def _clear_cache():
    cache.clear()
    yield
    cache.clear()


class Owner:
    def __init__(self, name):
        self.account, self.token = services.create_account(name, password='pw')
        self.api_token = services.create_api_token(self.account, 'test')[1]


@pytest.fixture
def owner(db):
    return Owner('alice')


@pytest.fixture
def other(db):
    return Owner('bob')


@pytest.fixture
def bee():
    return Bee.make(0, seed=7)


def save_sample(sample, values=None, protocol='aircraft', unit=2000):
    """Save `sample` with one range map (none if `values` is empty)."""
    from adsbee_swarm.models import SampleRange
    sample.save()
    if values:
        row = SampleRange(sample=sample, protocol=protocol, unit_m=unit)
        row.set_ranges(values)
        row.save()
    return sample


def post_report(client, token, body, **extra):
    return client.post('/api/swarm/v1/report', data=json.dumps(body), content_type='application/json',
                       HTTP_AUTHORIZATION=f'Bearer {token}', **extra)


@pytest.fixture
def rng():
    return random.Random(3)
