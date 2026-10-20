"""Fixed-window rate limits in the default cache, so every worker counts together."""
from __future__ import annotations

import hashlib
import time

from django.core.cache import cache

from . import conf


def hit(name: str, ident: str) -> int:
    """Count one request. 0 when allowed, else seconds until the window resets."""
    count, window = (int(part) for part in conf.get('RATE_LIMITS')[name].split('/'))
    now = time.time()
    bucket = int(now // window)
    key = f'swarm-rl:{name}:{hashlib.sha256(ident.encode()).hexdigest()[:32]}:{bucket}'
    if cache.add(key, 1, timeout=window + 1):
        used = 1
    else:
        try:
            used = cache.incr(key)
        except ValueError:
            cache.add(key, 1, timeout=window + 1)
            used = 1
    if used > count:
        return max(1, int((bucket + 1) * window - now) + 1)
    return 0
