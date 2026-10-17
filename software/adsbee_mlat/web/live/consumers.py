import asyncio

from channels.generic.websocket import AsyncWebsocketConsumer

from .relay import get_relay


class LiveConsumer(AsyncWebsocketConsumer):
    """Read-only live feed: the snapshot on connect, then every relayed message."""

    async def connect(self):
        await self.accept()
        self.relay = get_relay()
        self.client = await self.relay.add(lambda text: self.send(text_data=text))
        self.sender = asyncio.create_task(self.client.run())

    async def disconnect(self, code):
        if getattr(self, "client", None):
            self.relay.remove(self.client)
            self.sender.cancel()

    async def receive(self, text_data=None, bytes_data=None):
        pass
