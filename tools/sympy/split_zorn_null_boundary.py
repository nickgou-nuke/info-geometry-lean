#!/usr/bin/env python3
"""SymPy mirror for the split Zorn null-boundary finite identities."""

from pathlib import Path
import runpy

if __name__ == "__main__":
    runpy.run_path(str(Path(__file__).resolve().parents[2] / "proofs" / "split_zorn_null_boundary.py"), run_name="__main__")
