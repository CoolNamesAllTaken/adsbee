from django.contrib import admin

from .models import Receiver


@admin.register(Receiver)
class ReceiverAdmin(admin.ModelAdmin):
    list_display = ("receiver_id", "name", "owner", "enabled", "has_fixed_position", "updated")
    list_editable = ("enabled",)
    list_filter = ("enabled",)
    search_fields = ("receiver_id", "name", "owner")
    readonly_fields = ("created", "updated")
    fieldsets = (
        (None, {"fields": ("receiver_id", "name", "owner", "enabled")}),
        (
            "Fixed position override",
            {
                "fields": ("fixed_lat", "fixed_lon", "fixed_alt_m"),
                "description": "Used instead of the receiver's GNSS position when set.",
            },
        ),
        (None, {"fields": ("created", "updated")}),
    )

    @admin.display(boolean=True, description="Fixed position")
    def has_fixed_position(self, obj):
        return obj.has_fixed_position
