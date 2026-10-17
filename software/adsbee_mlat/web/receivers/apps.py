from django.apps import AppConfig


class ReceiversConfig(AppConfig):
    name = "receivers"
    verbose_name = "Receivers"

    def ready(self):
        from . import signals  # noqa: F401
