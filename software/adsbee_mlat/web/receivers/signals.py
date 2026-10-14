from django.db import transaction
from django.db.models.signals import post_delete, post_save
from django.dispatch import receiver

from .config import publish_config
from .models import Receiver


@receiver(post_save, sender=Receiver)
@receiver(post_delete, sender=Receiver)
def on_receiver_change(**kwargs):
    transaction.on_commit(publish_config)
