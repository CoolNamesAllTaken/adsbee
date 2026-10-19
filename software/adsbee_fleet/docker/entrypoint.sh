#!/bin/sh
set -e
python manage.py migrate --noinput
python manage.py createcachetable
# Retention once a day, beside the web server.
(while true; do python manage.py fleet_retention || true; sleep 86400; done) &
exec gunicorn example_site.wsgi --bind 0.0.0.0:8000 --workers "${GUNICORN_WORKERS:-3}" --access-logfile -
