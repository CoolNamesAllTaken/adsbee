#!/bin/sh
# Prepares the database, then runs the given command (the web server by default).
set -e
if [ "$1" = "uvicorn" ]; then
    python manage.py migrate --noinput -v0
    if [ -n "$DJANGO_SUPERUSER_USERNAME" ] && [ -n "$DJANGO_SUPERUSER_PASSWORD" ]; then
        python manage.py createsuperuser --noinput --email "${DJANGO_SUPERUSER_EMAIL:-admin@localhost}" 2>/dev/null \
            && echo "Created admin user $DJANGO_SUPERUSER_USERNAME" || true
    fi
    python manage.py publish_receiver_config || true
fi
exec "$@"
