# ADSBee MLAT server

Multilateration (MLAT) server for ADSBee receivers: the core (`core/`) locates aircraft from receiver timestamps, and
the web app (`web/`) shows them on a live map. Both run with Docker Compose, connected through Redis.

## Deploy

```bash
cd software/adsbee_mlat
cp .env.example .env        # set DJANGO_SECRET_KEY, the admin password and allowed hosts
docker compose up -d --build
```

- Map: `http://<server>:8080/` (read-only, public).
- Admin: `http://<server>:8080/admin/` with `DJANGO_SUPERUSER_USERNAME` / `DJANGO_SUPERUSER_PASSWORD` from `.env`.
- Receivers feed the core on port 31090 (TCP or UDP); see [PROTOCOL.md](PROTOCOL.md).
- Try the map without receivers: `docker compose --profile demo up -d redis web fake` plays synthetic traffic.

Update with `git pull && docker compose up -d --build`. Map and admin data (users, receiver settings) live in the
`web-data` volume.

## Receivers in the admin

Receivers appear in the admin once the core reports them. For each one you can set a name and owner, disable it
(hidden from the map and ignored by the solver), or override its position with a fixed latitude, longitude and
altitude.

## Map

- Aircraft are colored by altitude. ADS-B positions have a thin dark outline; MLAT positions have a red outline and a
  circle showing the 1 σ position error.
- Receivers are yellow dots, ringed green when their clock is in sync and red when not. Green lines join receivers
  that are synced with each other.
- Hover anything for details; click an aircraft for its panel and trail. The buttons on the right toggle layers.
