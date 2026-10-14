FROM python:3.12-slim

ENV PYTHONDONTWRITEBYTECODE=1 \
    PYTHONUNBUFFERED=1 \
    MLAT_DATA_DIR=/data

WORKDIR /app
COPY requirements.txt .
RUN pip install --no-cache-dir -r requirements.txt

COPY . .
RUN DJANGO_SECRET_KEY=build python manage.py collectstatic --noinput -v0 \
    && useradd --system --uid 1000 --home /app mlat \
    && mkdir -p /data && chown mlat /data
USER mlat

EXPOSE 8000
VOLUME /data
HEALTHCHECK --interval=15s --timeout=5s --start-period=20s --retries=3 \
    CMD python -c "import urllib.request; urllib.request.urlopen('http://127.0.0.1:8000/healthz', timeout=4)"
ENTRYPOINT ["./entrypoint.sh"]
CMD ["uvicorn", "mlat_web.asgi:application", "--host", "0.0.0.0", "--port", "8000", "--ws", "websockets", "--proxy-headers", "--forwarded-allow-ips", "*"]
