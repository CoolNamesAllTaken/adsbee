from django.core.management.base import BaseCommand

from adsbee_swarm import retention


class Command(BaseCommand):
    help = 'Roll hourly swarm samples older than ADSBEE_SWARM_HOURLY_RETENTION_DAYS into daily ones.'

    def add_arguments(self, parser):
        parser.add_argument('--dry-run', action='store_true')

    def handle(self, *args, dry_run=False, **options):
        result = retention.roll_up(dry_run=dry_run)
        self.stdout.write(f"{'would roll' if dry_run else 'rolled'} {result['hours']} hourly samples into "
                          f"{result['days']} days; {result['expired_days']} daily samples expired")
