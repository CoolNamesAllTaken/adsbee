"""Live stack for browser tests: redis-server, the web app under uvicorn and the fake publisher.

Needs `redis-server` on PATH (or REDIS_SERVER) and a Playwright Chromium (`playwright install chromium`,
or PLAYWRIGHT_CHROMIUM_EXECUTABLE). Set MLAT_E2E_MEDIA to a folder to keep screenshots and videos.
"""

import os
import shutil
import socket
import subprocess
import sys
import tempfile
import time
import urllib.request
from pathlib import Path

import pytest

WEB_DIR = Path(__file__).resolve().parent.parent


def free_port():
    with socket.socket() as s:
        s.bind(("127.0.0.1", 0))
        return s.getsockname()[1]


def wait_for(fn, timeout=20):
    end = time.time() + timeout
    while time.time() < end:
        try:
            if fn():
                return
        except Exception:
            pass
        time.sleep(0.2)
    raise TimeoutError


class Stack:
    def __init__(self, tmp):
        self.tmp = tmp
        self.procs = []
        self.redis_port = free_port()
        self.http_port = free_port()
        self.redis_url = f"redis://127.0.0.1:{self.redis_port}/0"
        self.url = f"http://127.0.0.1:{self.http_port}/"
        self.publisher = None

    def spawn(self, args, **kw):
        log = open(self.tmp / f"{Path(args[0]).name}-{len(self.procs)}.log", "w")
        p = subprocess.Popen(args, stdout=log, stderr=subprocess.STDOUT, **kw)
        self.procs.append(p)
        return p

    def start(self):
        redis_server = os.environ.get("REDIS_SERVER") or shutil.which("redis-server")
        self.spawn([redis_server, "--port", str(self.redis_port), "--save", "", "--appendonly", "no"])
        env = dict(os.environ, DJANGO_DEBUG="1", MLAT_DATA_DIR=str(self.tmp), REDIS_URL=self.redis_url,
                   DJANGO_SETTINGS_MODULE="mlat_web.settings")
        subprocess.run([sys.executable, "manage.py", "migrate", "-v0"], cwd=WEB_DIR, env=env, check=True)
        self.spawn([sys.executable, "-m", "uvicorn", "mlat_web.asgi:application", "--port", str(self.http_port),
                    "--ws", "websockets", "--log-level", "warning"], cwd=WEB_DIR, env=env)
        wait_for(lambda: urllib.request.urlopen(self.url + "healthz", timeout=2).status == 200)

    def publish(self, *args):
        """(Re)starts the fake publisher with the given arguments."""
        if self.publisher:
            self.publisher.terminate()
            self.publisher.wait()
        self.publisher = self.spawn([sys.executable, str(WEB_DIR / "tools" / "fake_publisher.py"),
                                     "--redis", self.redis_url, *args])

    def stop(self):
        for p in reversed(self.procs):
            p.terminate()
        for p in self.procs:
            try:
                p.wait(5)
            except subprocess.TimeoutExpired:
                p.kill()


def pytest_collection_modifyitems(config, items):
    if not (os.environ.get("REDIS_SERVER") or shutil.which("redis-server")):
        skip = pytest.mark.skip(reason="redis-server not found")
        for item in items:
            if "e2e" in item.keywords:
                item.add_marker(skip)


@pytest.fixture(scope="session")
def stack():
    with tempfile.TemporaryDirectory(prefix="mlat-e2e-") as tmp:
        s = Stack(Path(tmp))
        try:
            s.start()
            yield s
        finally:
            s.stop()


@pytest.fixture(scope="session")
def media_dir():
    d = os.environ.get("MLAT_E2E_MEDIA")
    if d:
        Path(d).mkdir(parents=True, exist_ok=True)
    return Path(d) if d else None


@pytest.fixture(scope="session")
def browser():
    from playwright.sync_api import sync_playwright

    with sync_playwright() as p:
        b = p.chromium.launch(executable_path=os.environ.get("PLAYWRIGHT_CHROMIUM_EXECUTABLE") or None)
        yield b
        b.close()


@pytest.fixture
def page(browser, media_dir, request):
    opts = {"viewport": {"width": 1400, "height": 850}}
    if media_dir:
        opts.update(record_video_dir=str(media_dir / "video"), record_video_size={"width": 1400, "height": 850})
    ctx = browser.new_context(**opts)
    pg = ctx.new_page()
    errors = []
    pg.on("pageerror", lambda e: errors.append(str(e)))
    yield pg
    ctx.close()
    if media_dir and pg.video:
        Path(pg.video.path()).rename(media_dir / f"{request.node.name}.webm")
    assert not errors, errors
