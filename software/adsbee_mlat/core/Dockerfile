FROM python:3.11-slim

WORKDIR /app
COPY pyproject.toml README.md ./
COPY adsbee_mlat ./adsbee_mlat
RUN pip install --no-cache-dir . && useradd --system mlat

ENV REDIS_URL=redis://redis:6379/0 \
    MLAT_FEED_PORT=31090 \
    MLAT_SBS_PORT=31003 \
    PYTHONUNBUFFERED=1

# Receiver feeds (TCP and UDP) and the SBS output of MLAT fixes.
EXPOSE 31090/tcp 31090/udp 31003/tcp

HEALTHCHECK --interval=30s --timeout=5s --start-period=10s \
    CMD python -c "import os, socket; socket.create_connection(('127.0.0.1', int(os.environ['MLAT_FEED_PORT'])), 2)"

USER mlat
CMD ["adsbee-mlat"]
