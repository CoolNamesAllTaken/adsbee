"""Visvalingam-Whyatt progressive line simplification -> importance-ordered
vertices for the `world.map` vector encoding.

Instead of baking one polyline per zoom level, we compute each vertex's VW
"effective area" (the triangle area it forms with its current neighbors when it
would be removed) ONCE. The device then reads the prefix of vertices whose
importance >= a pixel-derived threshold and draws them in original-sequence
order: one encoding, arbitrary simplification by thresholding, lines that keep a
roughly constant on-screen vertex density as you zoom out.

Why VW over Douglas-Peucker: VW's area metric thins smoothly and preserves
overall shape at low vertex counts, which reads better on a 1-bit e-paper map;
DP preserves spikes and thins more abruptly. (See plan sources.)

The importance values are MONOTONE in the removal order by construction here: we
remove the lowest-area vertex repeatedly and record the area *at removal*,
carrying forward max() so a vertex never has lower recorded importance than one
removed after it. This guarantees any threshold prefix is a valid, connected
simplification (the classic VW hierarchy property) with no parent pointers.
"""
import heapq


def _tri_area(a, b, c):
    """Twice the triangle area |(b-a) x (c-a)| for points (x,y)."""
    return abs((b[0] - a[0]) * (c[1] - a[1]) - (c[0] - a[0]) * (b[1] - a[1])) / 2.0


def effective_areas(points):
    """Compute VW effective area per vertex for a polyline `points` [(x,y),...].

    Returns a list `imp` (same length) where imp[i] is the effective area at
    which vertex i would be removed. Endpoints get +inf (never removed).
    Interior areas are made monotone-nondecreasing in removal order so prefixes
    are nested-valid.
    """
    n = len(points)
    if n <= 2:
        return [float("inf")] * n

    imp = [0.0] * n
    imp[0] = imp[-1] = float("inf")
    prev = list(range(-1, n - 1))   # prev[i] = previous live vertex index
    nxt = list(range(1, n + 1))     # nxt[i] = next live vertex index
    nxt[n - 1] = -1

    # lazy-deletion heap: entries are (area, version, i); a heap entry is valid
    # only if its version matches ver[i] (recompute bumps the version).
    heap = []
    ver = [0] * n
    alive = [True] * n

    def push(i):
        if prev[i] != -1 and nxt[i] != -1:
            a = _tri_area(points[prev[i]], points[i], points[nxt[i]])
            heapq.heappush(heap, (a, ver[i], i))

    for i in range(1, n - 1):
        push(i)

    running_max = 0.0
    removed = 0
    while removed < n - 2:
        a, v, i = heapq.heappop(heap)
        if not alive[i] or v != ver[i]:
            continue  # stale entry
        running_max = max(running_max, a)
        imp[i] = running_max
        alive[i] = False
        removed += 1
        p, q = prev[i], nxt[i]
        if p != -1:
            nxt[p] = q
        if q != -1:
            prev[q] = p
        for j in (p, q):
            if j != -1 and prev[j] != -1 and nxt[j] != -1:
                ver[j] += 1
                push(j)
    return imp


def order_by_importance(points, imp):
    """Return vertices as (x, y, seq, importance) sorted by descending
    importance (endpoints first). `seq` is the original index so the device can
    re-sort a threshold prefix back into draw order."""
    order = sorted(range(len(points)), key=lambda i: imp[i], reverse=True)
    out = []
    for i in order:
        x, y = points[i]
        out.append((x, y, i, imp[i]))
    return out
