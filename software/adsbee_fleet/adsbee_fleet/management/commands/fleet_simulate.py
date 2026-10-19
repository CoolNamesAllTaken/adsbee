"""Demo history: simulated bees on an account, one stored report per bee per hour, ending now."""
import random
from datetime import timedelta

from django.core.management.base import BaseCommand, CommandError
from django.utils import timezone

from adsbee_fleet import protocol
from adsbee_fleet.models import Account, Device
from adsbee_fleet.simulator import Bee


class Command(BaseCommand):
    help = 'Store simulated reports for an account (demos).'

    def add_arguments(self, parser):
        parser.add_argument('username')
        parser.add_argument('--bees', type=int, default=5)
        parser.add_argument('--hours', type=int, default=24 * 7)
        parser.add_argument('--seed', type=int, default=1)

    def handle(self, username, bees, hours, seed, **options):
        account = Account.objects.filter(user__username=username).first()
        if account is None:
            raise CommandError(f'no account {username}')
        rng = random.Random(seed)
        now = timezone.now()
        for index in range(bees):
            bee = Bee.make(index, seed)
            device, _ = Device.objects.get_or_create(account=account, product=bee.product, unique_id=bee.unique_id)
            if not device.label:
                device.label = bee.label
                device.save(update_fields=['label'])
            for hour in range(hours, 0, -1):
                protocol.ingest(device, protocol.parse(bee.report(rng=rng)), now - timedelta(hours=hour - 1))
            self.stdout.write(f'{bee.label}: {bee.unique_id} {hours} h')
