#!/usr/bin/env python3
"""QMS CLI entry point — delegates to tools.qms.qms_runner.main."""

from __future__ import annotations

import sys
from pathlib import Path

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))

from tools.qms.qms_runner import main

if __name__ == "__main__":
    raise SystemExit(main())
