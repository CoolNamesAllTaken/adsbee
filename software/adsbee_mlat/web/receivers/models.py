from django.core.exceptions import ValidationError
from django.core.validators import MaxValueValidator, MinValueValidator
from django.db import models


class Receiver(models.Model):
    """An ADSBee feeding the MLAT server. `receiver_id` matches the "id" the core reports."""

    receiver_id = models.CharField("ID", max_length=64, unique=True)
    name = models.CharField(max_length=100, blank=True)
    owner = models.CharField(max_length=100, blank=True, help_text="Person or group operating the receiver.")
    enabled = models.BooleanField(default=True, help_text="Disabled receivers are hidden from the map and ignored by the solver.")
    fixed_lat = models.FloatField(
        "fixed latitude", null=True, blank=True, validators=[MinValueValidator(-90), MaxValueValidator(90)]
    )
    fixed_lon = models.FloatField(
        "fixed longitude", null=True, blank=True, validators=[MinValueValidator(-180), MaxValueValidator(180)]
    )
    fixed_alt_m = models.FloatField("fixed altitude (m)", null=True, blank=True)
    created = models.DateTimeField(auto_now_add=True)
    updated = models.DateTimeField(auto_now=True)

    class Meta:
        ordering = ["name", "receiver_id"]

    def __str__(self):
        return self.name or self.receiver_id

    @property
    def has_fixed_position(self):
        return self.fixed_lat is not None and self.fixed_lon is not None

    def clean(self):
        if (self.fixed_lat is None) != (self.fixed_lon is None):
            raise ValidationError("Set both fixed latitude and longitude, or neither.")
        if self.fixed_alt_m is not None and not self.has_fixed_position:
            raise ValidationError("A fixed altitude needs a fixed latitude and longitude.")

    def config(self):
        """Entry for the receiver config published to Redis."""
        fixed = None
        if self.has_fixed_position:
            fixed = {"lat": self.fixed_lat, "lon": self.fixed_lon, "alt_m": self.fixed_alt_m}
        return {"name": self.name, "owner": self.owner, "enabled": self.enabled, "fixed": fixed}
