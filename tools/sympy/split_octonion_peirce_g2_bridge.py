#!/usr/bin/env python3
"""Bridge the integer Peirce-Witt split-octonion atoms to the F2 G2 lane.

This is a narrow coordinate bridge:

* start with the integer Zorn atoms from the symplectic foundation slice;
* reduce their eight coordinates modulo two;
* compare the results with the F2 split-octonion atoms used by
  `g2_2_automorphism_theorem.py`.

It does not assert Cuntz closure, wallpaper forcing, braid coherence, or a
global real automorphism classification.
"""
from __future__ import annotations

import importlib.util
from pathlib import Path
import sys
from typing import Any

ROOT = Path(__file__).resolve().parents[2]


def load_module(path: Path, name: str) -> Any:
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


symp = load_module(ROOT / "tools/sympy/split_octonion_symplectic_foundation.py", "split_oct_symp")
g2 = load_module(ROOT / "tools/sympy/g2_2_automorphism_theorem.py", "g2_2_auto")


def reduce_zorn_to_f2(z: Any) -> tuple[int, int, int, int, int, int, int, int]:
    coords = (z.a, z.b, z.x[0], z.x[1], z.x[2], z.y[0], z.y[1], z.y[2])
    return tuple(int(c) % 2 for c in coords)  # type: ignore[return-value]


def main() -> None:
    assert reduce_zorn_to_f2(symp.one) == g2.ONE
    assert reduce_zorn_to_f2(symp.H) == g2.ONE
    assert reduce_zorn_to_f2(symp.ePlus) == g2.EPLUS
    assert reduce_zorn_to_f2(symp.eMinus) == g2.EMINUS
    for i in range(3):
        assert reduce_zorn_to_f2(symp.up[i]) == g2.UP[i]
        assert reduce_zorn_to_f2(symp.down[i]) == g2.DOWN[i]
        assert reduce_zorn_to_f2(symp.comm(symp.up[i], symp.down[i])) == g2.ONE
        assert reduce_zorn_to_f2(symp.anticomm(symp.up[i], symp.down[i])) == g2.ONE

    print("SPLIT_OCTONION_PEIRCE_G2_BRIDGE_OK")
    print("scope: integer Peirce-Witt atoms reduce to F2 G2 split-octonion coordinates only")


if __name__ == "__main__":
    main()
