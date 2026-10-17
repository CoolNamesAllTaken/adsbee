import json
import time

import redis
from django.conf import settings
from django.db import connection
from django.http import JsonResponse
from django.shortcuts import render

from .relay import get_relay


def map_view(request):
    config = {"ws": "ws/live", "tiles": settings.MAP_TILES, "start": None}
    try:
        lat, lon, zoom = (float(v) for v in settings.MAP_START.split(","))
        config["start"] = [lat, lon, zoom]
    except ValueError:
        pass
    return render(request, "live/map.html", {"config": json.dumps(config)})


def healthz(request):
    status = {"db": False, "redis": False}
    try:
        with connection.cursor() as c:
            c.execute("SELECT 1")
        status["db"] = True
    except Exception:
        pass
    try:
        status["redis"] = bool(redis.Redis.from_url(settings.REDIS_URL, socket_timeout=2).ping())
    except redis.RedisError:
        pass
    last = get_relay().last_message_time
    status["core_age_s"] = None if last is None else round(time.time() - last, 1)
    ok = status["db"] and status["redis"]
    return JsonResponse(status, status=200 if ok else 503)
