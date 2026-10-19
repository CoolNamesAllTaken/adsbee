# adsbee_fleet

A fleet server for ADSBee receivers. Each bee reports hourly: message counts, a range map, its
firmware. You get a map of your bees, how far each one hears per altitude, and staged firmware
targets. It is a reusable Django app (GPL-3.0) with a plain reference UI; adsbee.aero runs the same
app behind its own pages.

- Protocol and API: [docs/fleet_api.md](docs/fleet_api.md), [adsbee_fleet/openapi.yaml](adsbee_fleet/openapi.yaml)
- Simulator: `python -m adsbee_fleet.simulator --server <url> --token <enroll token>`

## Self-host

Needs Docker and a DNS name pointing at the host.

```sh
cd software/adsbee_fleet/docker
cp env.example .env               # set FLEET_DOMAIN, POSTGRES_PASSWORD, DJANGO_SECRET_KEY
docker compose up -d --build
docker compose exec app python manage.py fleet_account create me --password '<password>'
```

The last command prints your **enroll token**. Sign in at `https://<FLEET_DOMAIN>/`. Caddy gets the
TLS certificate. `fleet_account` also does `grant`, `revoke`, `disable`, `enable` and `rotate`;
`/admin/` works for a superuser (`manage.py createsuperuser`).

Retention runs daily in the `app` container (`manage.py fleet_retention`): hourly rows older than
365 days become daily rows. Change it with `ADSBEE_FLEET_HOURLY_RETENTION_DAYS`.

## Point a bee at it

In the bee's console:

```
AT+FLEET=1,https://<FLEET_DOMAIN>,<enroll token>
AT+FLEET?
```

The bee shows up after its first report, 2–5 minutes after boot. It installs rollout targets only
when `AT+AUTO_UPDATE=1`. Rotating the enroll token (⚿ page) cuts off every bee holding the old one.

## In another Django project

```python
INSTALLED_APPS += ['adsbee_fleet']
urlpatterns += [path('', include('adsbee_fleet.api_urls')),          # device + user API
                path('fleet/', include('adsbee_fleet.urls'))]         # reference UI (optional)
ADSBEE_FLEET_DEVICE_VERIFIER = 'myapp.keys.verify_fleet_report'      # (request, report, account) -> bool
```

`adsbee_fleet.services` has what staff pages need: `create_account`, `grant`, `revoke`,
`set_disabled`, `rotate_enroll_token`, `create_api_token`. Settings are listed in `adsbee_fleet/conf.py`.

## Develop

```sh
poetry install --with dev
poetry run pytest
poetry run python manage.py migrate && poetry run python manage.py createcachetable
poetry run python manage.py fleet_account create demo --password demo
poetry run python manage.py fleet_simulate demo --bees 5 --hours 168
DJANGO_DEBUG=1 poetry run python manage.py runserver
```
