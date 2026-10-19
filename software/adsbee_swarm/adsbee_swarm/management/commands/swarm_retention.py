from django.core.management.base import BaseCommand

from adsbee_swarm import retention


class Command(BaseCommand):
    help = ('Delete hourly swarm samples older than ADSBEE_SWARM_HOURLY_RETENTION_DAYS, after checking '
            'each of their days against its daily row.')

    def add_arguments(self, parser):
        parser.add_argument('--dry-run', action='store_true')
        parser.add_argument('--backfill', action='store_true',
                            help='Rebuild the daily row of every day that has hourly rows; delete nothing.')

    def handle(self, *args, dry_run=False, backfill=False, **options):
        result = retention.roll_up(dry_run=dry_run, backfill=backfill)
        verb = 'would check' if dry_run else 'checked'
        self.stdout.write(f"{verb} {result['days']} days ({result['hours']} hourly samples): "
                          f"{result['fixed_days']} daily rows fixed; "
                          f"{'kept' if backfill else 'deleted'} the hourly samples; "
                          f"{result['expired_days']} daily samples expired")
