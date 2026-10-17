from django.core.management.base import BaseCommand, CommandError

from receivers.config import publish_config


class Command(BaseCommand):
    help = "Publish the receiver config to Redis for the MLAT core."

    def handle(self, *args, **options):
        if not publish_config():
            raise CommandError("Redis unreachable")
        self.stdout.write("Published receiver config.")
