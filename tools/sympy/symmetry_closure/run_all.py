#!/usr/bin/env python3
"""Run all finite SymPy shadows for the symmetry-closure audit lane."""

from __future__ import annotations

import importlib.util
from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT))

MODULES = [
    "sector_closure_conformal_blocks",
    "closure_involution_five_grade",
    "hestenes_krein_superbracket_closure",
    "operator_cartan_superbracket_closure",
    "kkt_closure_symmetry",
    "supercharge_central_charge_closure",
    "split_triality_kernel",
    "z3_yang_baxter",
    "holographic_entanglement_triality",
]


def load_module(name: str):
    path = ROOT / f"{name}.py"
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"could not load {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def main() -> None:
    for name in MODULES:
        print(f"\n=== {name} ===")
        module = load_module(name)
        module.run()
    print("\nAll finite SymPy symmetry-closure shadows passed.")


if __name__ == "__main__":
    main()
