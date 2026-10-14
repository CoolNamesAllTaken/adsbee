from django.contrib import admin
from django.urls import path

from live import views

admin.site.site_header = "ADSBee MLAT"
admin.site.site_title = "ADSBee MLAT"

urlpatterns = [
    path("", views.map_view, name="map"),
    path("healthz", views.healthz, name="healthz"),
    path("admin/", admin.site.urls),
]
