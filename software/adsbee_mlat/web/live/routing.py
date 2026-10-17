from django.urls import path

from .consumers import LiveConsumer

websocket_urlpatterns = [path("ws/live", LiveConsumer.as_asgi())]
