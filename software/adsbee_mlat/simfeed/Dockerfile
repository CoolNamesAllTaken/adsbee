# Build context: software/adsbee_mlat
FROM python:3.11-slim

WORKDIR /app
COPY sim ./sim
COPY core ./core
RUN pip install --no-cache-dir ./sim ./core
COPY simfeed/simfeed.py ./

ENTRYPOINT ["python", "simfeed.py"]
