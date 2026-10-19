# adsbee_swarm

A swarm server for ADSBee receivers. Each bee reports hourly: message counts, a range map, its
firmware. You get a map of your bees, how far each one hears per altitude, and staged firmware
targets. It is a reusable Django app (GPL-3.0) with a plain reference UI; adsbee.aero runs the same
app behind its own pages.

- Protocol and API: [docs/swarm_api.md](docs/swarm_api.md), [adsbee_swarm/openapi.yaml](adsbee_swarm/openapi.yaml)
- Simulator: `python -m adsbee_swarm.simulator --server <url> --token <enroll token>`

## Self-host

Needs Docker and a DNS name pointing at the host.

```sh
cd software/adsbee_swarm/docker
cp env.example .env               # set SWARM_DOMAIN, POSTGRES_PASSWORD, DJANGO_SECRET_KEY
docker compose up -d --build
docker compose exec app python manage.py swarm_account create me --password '<password>'
```

The last command prints your **enroll token**. Sign in at `https://<SWARM_DOMAIN>/`. Caddy gets the
TLS certificate. `swarm_account` also does `grant`, `revoke`, `disable`, `enable` and `rotate`;
`/admin/` works for a superuser (`manage.py createsuperuser`).

Each bee gets an hourly and a daily row from its first report; windows over 3 days read the daily
rows. Retention runs daily in the `app` container (`manage.py swarm_retention`): hourly rows older
than 90 days are deleted, daily rows are kept. Change it with `ADSBEE_SWARM_HOURLY_RETENTION_DAYS`.

## Point a bee at it

In the bee's console:

```
AT+SWARM=1,https://<SWARM_DOMAIN>,<enroll token>
AT+SWARM?
```

The bee shows up after its first report, 2–5 minutes after boot. It installs rollout targets only
when `AT+AUTO_UPDATE=1`. Rotating the enroll token (⚿ page) cuts off every bee holding the old one.

## In another Django project

```python
INSTALLED_APPS += ['adsbee_swarm']
urlpatterns += [path('', include('adsbee_swarm.api_urls')),          # device + user API
                path('swarm/', include('adsbee_swarm.urls'))]         # reference UI (optional)
ADSBEE_SWARM_DEVICE_VERIFIER = 'myapp.keys.verify_swarm_report'      # (request, report, account) -> bool
```

`adsbee_swarm.services` has what staff pages need: `create_account`, `grant`, `revoke`,
`set_disabled`, `rotate_enroll_token`, `create_api_token`. Settings are listed in `adsbee_swarm/conf.py`.

## Develop

```sh
poetry install --with dev
poetry run pytest
poetry run python manage.py migrate && poetry run python manage.py createcachetable
poetry run python manage.py swarm_account create demo --password demo
poetry run python manage.py swarm_simulate demo --bees 5 --hours 168
DJANGO_DEBUG=1 poetry run python manage.py runserver
```
