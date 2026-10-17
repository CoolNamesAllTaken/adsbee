import json
from unittest import mock

import fakeredis
import pytest
from django.core.exceptions import ValidationError

from receivers.config import CONFIG_CHANNEL, CONFIG_KEY, build_config, publish_config
from receivers.models import Receiver

pytestmark = pytest.mark.django_db


def test_fixed_position_needs_lat_and_lon():
    with pytest.raises(ValidationError):
        Receiver(receiver_id="a", fixed_lat=37.0).full_clean()
    with pytest.raises(ValidationError):
        Receiver(receiver_id="a", fixed_alt_m=10).full_clean()
    with pytest.raises(ValidationError):
        Receiver(receiver_id="a", fixed_lat=91, fixed_lon=0).full_clean()
    Receiver(receiver_id="a", fixed_lat=37.0, fixed_lon=-122.0, fixed_alt_m=12).full_clean()


def test_config_contents():
    Receiver.objects.create(receiver_id="bee-1", name="Roof", owner="Ana", fixed_lat=1.5, fixed_lon=2.5)
    Receiver.objects.create(receiver_id="bee-2", enabled=False)
    cfg = build_config()["receivers"]
    assert cfg["bee-1"] == {"name": "Roof", "owner": "Ana", "enabled": True,
                            "fixed": {"lat": 1.5, "lon": 2.5, "alt_m": None}}
    assert cfg["bee-2"]["enabled"] is False
    assert cfg["bee-2"]["fixed"] is None


def test_publish_config_sets_key_and_notifies():
    r = fakeredis.FakeRedis()
    sub = r.pubsub()
    sub.subscribe(CONFIG_CHANNEL)
    sub.get_message(timeout=1)
    Receiver.objects.create(receiver_id="bee-1", name="Roof")
    assert publish_config(r)
    assert json.loads(r.get(CONFIG_KEY))["receivers"]["bee-1"]["name"] == "Roof"
    msg = sub.get_message(timeout=1)
    assert json.loads(msg["data"])["receivers"]["bee-1"]["name"] == "Roof"


def test_publish_config_survives_redis_down():
    r = mock.Mock()
    r.pipeline.side_effect = __import__("redis").ConnectionError("down")
    assert publish_config(r) is False


def test_save_and_delete_publish(django_capture_on_commit_callbacks):
    with mock.patch("receivers.signals.publish_config") as pub:
        with django_capture_on_commit_callbacks(execute=True):
            rx = Receiver.objects.create(receiver_id="bee-1")
        with django_capture_on_commit_callbacks(execute=True):
            rx.delete()
    assert pub.call_count == 2


def test_admin_list_and_edit(admin_client):
    Receiver.objects.create(receiver_id="bee-1", name="Roof")
    assert b"Roof" in admin_client.get("/admin/receivers/receiver/").content
    rx = Receiver.objects.get()
    with mock.patch("receivers.signals.publish_config"):
        resp = admin_client.post(f"/admin/receivers/receiver/{rx.pk}/change/", {
            "receiver_id": "bee-1", "name": "Tower", "owner": "", "enabled": "on",
            "fixed_lat": "37.5", "fixed_lon": "", "fixed_alt_m": "",
        })
    assert resp.status_code == 200  # Form error: longitude missing.
    assert b"Set both fixed latitude and longitude" in resp.content


def test_admin_requires_login(client):
    assert client.get("/admin/receivers/receiver/").status_code == 302
