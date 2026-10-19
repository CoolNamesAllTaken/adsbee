from django.contrib import admin

from .models import Account, ApiToken, Device, Rollout, Sample


@admin.register(Account)
class AccountAdmin(admin.ModelAdmin):
    list_display = ('user', 'privileges', 'disabled', 'enroll_token_prefix', 'created_at')
    list_filter = ('disabled',)
    search_fields = ('user__username', 'user__email')
    readonly_fields = ('enroll_token_hash', 'enroll_token_prefix', 'enroll_token_rotated_at')


@admin.register(ApiToken)
class ApiTokenAdmin(admin.ModelAdmin):
    list_display = ('prefix', 'name', 'account', 'created_at', 'last_used_at')
    readonly_fields = ('token_hash', 'prefix')


@admin.register(Device)
class DeviceAdmin(admin.ModelAdmin):
    list_display = ('unique_id', 'label', 'product', 'account', 'last_report_at', 'auto_update', 'removed_at')
    list_filter = ('product', 'auto_update')
    search_fields = ('unique_id', 'label', 'account__user__username')


@admin.register(Rollout)
class RolloutAdmin(admin.ModelAdmin):
    list_display = ('tag', 'product', 'account', 'scope', 'stage', 'paused', 'cancelled_at', 'created_at')
    filter_horizontal = ('devices', 'test_devices')


@admin.register(Sample)
class SampleAdmin(admin.ModelAdmin):
    list_display = ('device', 'start', 'span_s', 'reports', 'es_valid', 'aircraft_max')
    list_filter = ('span_s',)
