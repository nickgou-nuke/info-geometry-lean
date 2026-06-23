#!/usr/bin/env python3
"""SymPy mirror for the finite Cantor/split-null bridge."""

from pathlib import Path
import runpy

if __name__ == "__main__":
    runpy.run_path(
        str(Path(__file__).resolve().parents[2] / "proofs" / "cantor_split_null_bridge.py"),
        run_name="__main__",
    )
