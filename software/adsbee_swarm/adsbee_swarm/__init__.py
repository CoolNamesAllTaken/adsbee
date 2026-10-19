"""ADSBee swarm server: device reports, range maps, staged firmware targets. GPL-3.0."""
__version__ = '0.1.0'


class VerifierUnavailable(Exception):
    """Raised by a DEVICE_VERIFIER that cannot decide now (e.g. no keys loaded): the report is
    answered 503 with Retry-After, and the bee backs off and retries. Not a verdict on the bee."""

    def __init__(self, detail: str = '', retry_after: int | None = None):
        super().__init__(detail)
        self.detail = detail
        self.retry_after = retry_after
