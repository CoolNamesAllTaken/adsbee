"""python -m adsbee_mlat [--config FILE]"""

import argparse
import asyncio
import logging

from . import config
from .server import Server


def main():
    ap = argparse.ArgumentParser(description="ADSBee MLAT server")
    ap.add_argument("--config", help="TOML configuration file (default: $MLAT_CONFIG)")
    ap.add_argument("--log-level", default="INFO")
    args = ap.parse_args()
    logging.basicConfig(level=args.log_level, format="%(asctime)s %(levelname)s %(name)s: %(message)s")
    cfg = config.load(args.config)
    try:
        asyncio.run(Server(cfg).run_forever())
    except KeyboardInterrupt:
        pass


if __name__ == "__main__":
    main()
