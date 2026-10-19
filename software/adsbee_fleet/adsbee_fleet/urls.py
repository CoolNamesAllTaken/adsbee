"""The reference UI. Include with namespace: `path('fleet/', include('adsbee_fleet.urls'))`."""
from django.urls import path

from . import views

app_name = 'adsbee_fleet'

urlpatterns = [
    path('', views.device_list, name='devices'),
    path('devices/<int:pk>/', views.device_detail, name='device'),
    path('rollouts/', views.rollout_page, name='rollouts'),
    path('account/', views.account_page, name='account'),
    path('account/action/', views.account_action, name='account_action'),
]
