#!/usr/bin/env python3
"""Finite 1+3 slot verifier for the Zorn split-octonion basis.

Companion to:
  lean/InfoGeometry/OperatorAlgebra/SplitOctonionOnePlusThree.lean

Scope: exact split-octonion basis bookkeeping only.  This verifies the finite
`1 + 3` Zorn-vector decomposition used as a safe algebraic stepping stone:

  * diagonal idempotents e_+, e_-;
  * three upper vector slots u_i and three lower vector slots v_i;
  * diagonal projectors absorb the appropriate side and annihilate the opposite;
  * paired upper/lower products read back the diagonal idempotents;
  * cyclic products close as the cross-product table.

It does not prove a G2(2) automorphism theorem, an SU(3) color-stabilizer
theorem, or any particle-classification statement.
"""
from __future__ import annotations

import importlib.util
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
MULT_PATH = ROOT / "tools" / "sympy" / "split_octonion_multiplication.py"

spec = importlib.util.spec_from_file_location("split_octonion_multiplication", MULT_PATH)
assert spec is not None and spec.loader is not None
mult = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = mult
spec.loader.exec_module(mult)

ZERO = mult.ZERO
EPLUS = mult.EPLUS
EMINUS = mult.EMINUS
UP = mult.UP
DOWN = mult.DOWN
Zorn = mult.Zorn
BASIS_VEC = mult.BASIS_VEC
assert_eq = mult.assert_eq


def neg_down(k: int):
    return Zorn(0, 0, (0, 0, 0), tuple(-c for c in BASIS_VEC[k]))


def neg_up(k: int):
    return Zorn(0, 0, tuple(-c for c in BASIS_VEC[k]), (0, 0, 0))


def verify_one_plus_three_slots() -> None:
    assert_eq(EPLUS * EPLUS, EPLUS, "e+ idempotent")
    assert_eq(EMINUS * EMINUS, EMINUS, "e- idempotent")
    assert_eq(EPLUS * EMINUS, ZERO, "e+e- orthogonal")
    assert_eq(EMINUS * EPLUS, ZERO, "e-e+ orthogonal")

    for i in range(3):
        assert_eq(EPLUS * UP[i], UP[i], f"e+ absorbs u{i} from left")
        assert_eq(UP[i] * EMINUS, UP[i], f"u{i} absorbs e- from right")
        assert_eq(EMINUS * UP[i], ZERO, f"e- annihilates u{i} from left")
        assert_eq(UP[i] * EPLUS, ZERO, f"u{i} annihilates e+ from right")

        assert_eq(EMINUS * DOWN[i], DOWN[i], f"e- absorbs v{i} from left")
        assert_eq(DOWN[i] * EPLUS, DOWN[i], f"v{i} absorbs e+ from right")
        assert_eq(EPLUS * DOWN[i], ZERO, f"e+ annihilates v{i} from left")
        assert_eq(DOWN[i] * EMINUS, ZERO, f"v{i} annihilates e- from right")

        assert_eq(UP[i] * UP[i], ZERO, f"u{i} nil-square")
        assert_eq(DOWN[i] * DOWN[i], ZERO, f"v{i} nil-square")
        assert_eq(UP[i] * DOWN[i], EPLUS, f"u{i}v{i}=e+")
        assert_eq(DOWN[i] * UP[i], EMINUS, f"v{i}u{i}=e-")
        assert UP[i].det() == 0, f"u{i} null norm"
        assert DOWN[i].det() == 0, f"v{i} null norm"

    for i, j, k in [(0, 1, 2), (1, 2, 0), (2, 0, 1)]:
        assert_eq(UP[i] * UP[j], DOWN[k], f"u{i}u{j}=v{k}")
        assert_eq(UP[j] * UP[i], neg_down(k), f"u{j}u{i}=-v{k}")
        assert_eq(DOWN[i] * DOWN[j], neg_up(k), f"v{i}v{j}=-u{k}")
        assert_eq(DOWN[j] * DOWN[i], UP[k], f"v{j}v{i}=u{k}")


def verify_sage_g2_root_count_if_available() -> str:
    """Optional external sanity check only; not used as proof authority."""
    sage = Path("/home/goutev/miniforge3/envs/sage/bin/sage")
    if not sage.exists():
        return "SAGE_G2_ROOT_COUNT_SKIPPED"
    cmd = [
        str(sage),
        "-c",
        "R=RootSystem(['G',2]); print('SAGE_G2_ROOT_COUNT', len(list(R.root_poset())), 'rank', len(R.index_set()))",
    ]
    out = subprocess.check_output(cmd, text=True).strip()
    if "SAGE_G2_ROOT_COUNT 6 rank 2" not in out:
        raise AssertionError(out)
    return out


def main() -> None:
    verify_one_plus_three_slots()
    sage_line = verify_sage_g2_root_count_if_available()
    print("OK split_octonion_one_plus_three_slots: finite 1+3 slot laws verified")
    print(sage_line)
    print("scope: Zorn basis-slot algebra only; no G2(2), SU(3), or particle theorem claimed")


if __name__ == "__main__":
    main()
