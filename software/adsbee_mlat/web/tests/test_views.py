import json
from unittest import mock

import pytest

pytestmark = pytest.mark.django_db


def test_map_page(client, settings):
    settings.MAP_START = "37.4,-122.1,9"
    resp = client.get("/")
    assert resp.status_code == 200
    cfg = json.loads(resp.context["config"])
    assert cfg["ws"] == "ws/live" and cfg["start"] == [37.4, -122.1, 9.0]
    assert b"map.js" in resp.content


def test_map_page_without_start(client, settings):
    settings.MAP_START = ""
    assert json.loads(client.get("/").context["config"])["start"] is None


def test_healthz(client):
    with mock.patch("live.views.redis.Redis.from_url") as from_url:
        from_url.return_value.ping.return_value = True
        resp = client.get("/healthz")
    assert resp.status_code == 200 and resp.json()["redis"] is True


def test_healthz_redis_down(client, settings):
    settings.REDIS_URL = "redis://127.0.0.1:1/0"
    resp = client.get("/healthz")
    assert resp.status_code == 503 and resp.json()["redis"] is False
