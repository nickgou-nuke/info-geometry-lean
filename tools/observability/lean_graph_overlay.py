#!/usr/bin/env python3
"""Compatibility wrapper for the observability graph overlay CLI."""

from __future__ import annotations

import runpy
from pathlib import Path
import sys


def main() -> int:
    script = (
        Path(__file__).resolve().parent
        / "graph_overlay_toolchain"
        / "graph_overlay"
        / "scripts"
        / "lean_graph_overlay.py"
    )
    runpy.run_path(str(script), run_name="__main__")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
