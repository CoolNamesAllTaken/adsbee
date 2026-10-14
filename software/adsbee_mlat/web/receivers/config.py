"""Receiver config shared with the MLAT core through Redis.

Key `mlat:receiver_config` holds {"t": unix_s, "receivers": {id: {"name", "owner", "enabled", "fixed"}}},
where "fixed" is {"lat", "lon", "alt_m"} or null. The same JSON is published on channel `mlat:config`
whenever it changes.
"""

import json
import logging
import time

import redis
from django.conf import settings

from .models import Receiver

CONFIG_KEY = "mlat:receiver_config"
CONFIG_CHANNEL = "mlat:config"

log = logging.getLogger(__name__)


def build_config():
    return {"t": time.time(), "receivers": {r.receiver_id: r.config() for r in Receiver.objects.all()}}


def publish_config(client=None):
    """Write the config key and notify subscribers. Returns False when Redis is unreachable."""
    payload = json.dumps(build_config())
    try:
        client = client or redis.Redis.from_url(settings.REDIS_URL, socket_timeout=2)
        pipe = client.pipeline()
        pipe.set(CONFIG_KEY, payload)
        pipe.publish(CONFIG_CHANNEL, payload)
        pipe.execute()
        return True
    except redis.RedisError as e:
        log.warning("Could not publish receiver config: %s", e)
        return False
