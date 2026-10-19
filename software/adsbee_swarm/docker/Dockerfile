FROM python:3.12-slim
ENV PYTHONDONTWRITEBYTECODE=1 PYTHONUNBUFFERED=1
WORKDIR /app
RUN pip install --no-cache-dir "poetry>=2.1,<3" && poetry config virtualenvs.create false
COPY pyproject.toml poetry.lock README.md ./
COPY adsbee_swarm ./adsbee_swarm
RUN poetry install --only main --extras server --no-interaction
COPY example_site ./example_site
COPY manage.py ./
COPY docker/entrypoint.sh /entrypoint.sh
RUN STATIC_ROOT=/app/static python manage.py collectstatic --noinput
ENV STATIC_ROOT=/app/static
EXPOSE 8000
ENTRYPOINT ["/entrypoint.sh"]
