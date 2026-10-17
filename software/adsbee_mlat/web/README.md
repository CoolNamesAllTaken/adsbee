# MLAT web app

Django app serving the live map and the receiver admin. A single Redis subscription per process relays the core's
channels (`mlat:aircraft`, `mlat:receivers`, `mlat:stats`) to browsers over the `ws/live` WebSocket; new browsers get
`mlat:snapshot` first. Admin changes to receivers are written to `mlat:receiver_config` and announced on `mlat:config`
for the core. See `live/relay.py` for the message formats.

## Development

```bash
python3 -m venv .venv && .venv/bin/pip install -r requirements-dev.txt
redis-server --port 6379 &
export DJANGO_DEBUG=1
.venv/bin/python manage.py migrate
.venv/bin/uvicorn mlat_web.asgi:application --port 8000 --ws websockets &
.venv/bin/python tools/fake_publisher.py --aircraft 200      # synthetic traffic
```

`tools/fake_publisher.py --help` also covers recording and replaying traffic.

## Tests

```bash
.venv/bin/playwright install chromium
.venv/bin/pytest            # unit tests, plus browser tests when redis-server is on PATH
```

Browser tests start their own Redis, web server and fake publisher. They check that every fix reaches the map at
its own rate, that aircraft move every frame, and the frame cost with 1000 aircraft at 10 Hz. Set `MLAT_E2E_MEDIA`
to a folder to keep screenshots and videos.
