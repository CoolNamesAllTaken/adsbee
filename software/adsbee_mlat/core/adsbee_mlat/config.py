"""Server configuration: a TOML file plus environment variables."""

import os
import tomllib
from dataclasses import dataclass, field


@dataclass
class ReceiverConfig:
    """A receiver known in advance, typically a plain Beast feeder without receiver info frames."""

    id: str
    lat: float
    lon: float
    alt: float
    clock_hz: int = 12_000_000
    name: str | None = None
    uuid: str | None = None  # Matches a 0xe4 feed ID frame.
    peer: str | None = None  # Matches the source address of an incoming connection.
    connect: str | None = None  # host:port of a Beast output the server connects to.


@dataclass
class Config:
    listen_host: str = "0.0.0.0"
    listen_port: int = 31090
    udp: bool = True
    sbs_port: int | None = 31003
    redis_url: str | None = "redis://localhost:6379/0"
    group_window_s: float = 0.3
    publish_mlat_for_adsb: bool = False
    aircraft_interval_s: float = 0.1
    status_interval_s: float = 1.0
    receivers: list = field(default_factory=list)


def _host_port(s, default_port):
    host, _, port = s.rpartition(":")
    return (host or "0.0.0.0"), int(port or default_port)


def load(path=None, env=os.environ):
    """Reads the TOML file at path (or MLAT_CONFIG), then applies environment overrides."""
    cfg = Config()
    path = path or env.get("MLAT_CONFIG")
    data = {}
    if path:
        with open(path, "rb") as f:
            data = tomllib.load(f)
    server = data.get("server", {})
    if "listen" in server:
        cfg.listen_host, cfg.listen_port = _host_port(server["listen"], cfg.listen_port)
    cfg.udp = server.get("udp", cfg.udp)
    if "sbs_port" in server:
        cfg.sbs_port = server["sbs_port"] or None
    cfg.redis_url = server.get("redis_url", cfg.redis_url)
    cfg.group_window_s = float(server.get("group_window_s", cfg.group_window_s))
    cfg.publish_mlat_for_adsb = bool(server.get("publish_mlat_for_adsb", cfg.publish_mlat_for_adsb))
    for r in data.get("receiver", []):
        match = r.get("match", {})
        cfg.receivers.append(ReceiverConfig(
            id=str(r["id"]), lat=float(r["lat"]), lon=float(r["lon"]), alt=float(r.get("alt", 0.0)),
            clock_hz=int(r.get("clock_hz", 12_000_000)), name=r.get("name"), uuid=match.get("uuid"),
            peer=match.get("peer"), connect=r.get("connect")))
    if "REDIS_URL" in env:
        cfg.redis_url = env["REDIS_URL"] or None
    if "MLAT_LISTEN_PORT" in env:
        cfg.listen_port = int(env["MLAT_LISTEN_PORT"])
    if "MLAT_SBS_PORT" in env:
        cfg.sbs_port = int(env["MLAT_SBS_PORT"]) or None
    return cfg
