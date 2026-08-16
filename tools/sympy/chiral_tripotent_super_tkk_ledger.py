#!/usr/bin/env python3
"""Finite chiral / tripotent / Super-TKK hierarchy witness.

This mirrors `InfoGeometry.OperatorAlgebra.ChiralTripotentSuperTKKLedger`.
It checks only finite algebraic routing:
  * chiral projectors uPlus/uMinus are idempotent, orthogonal, and sum to I;
  * eps = uPlus - uMinus and a conformal atom K squares to -I;
  * tripotent states {-1,0,+1} satisfy x^3=x with projector partition;
  * a symbolic five-grade bracket table routes mixed/same arrows into g0/g±2.

No physical BdG, CPT, Pin(5,5), QCD, GR, or braid-statistics theorem is tested.
"""

from __future__ import annotations

import sys
from pathlib import Path
import sympy as sp

_REPO_ROOT = Path(__file__).resolve().parents[2]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

from tools.sympy.common import assert_matrix_eq


def main() -> None:
    I2 = sp.eye(2)
    Z2 = sp.zeros(2)
    u_plus = sp.Matrix([[1, 0], [0, 0]])
    u_minus = sp.Matrix([[0, 0], [0, 1]])
    eps = sp.diag(1, -1)
    boost = sp.Matrix([[0, 1], [1, 0]])
    K = boost * eps

    assert_matrix_eq("u+ idempotent", u_plus * u_plus, u_plus)
    assert_matrix_eq("u- idempotent", u_minus * u_minus, u_minus)
    assert_matrix_eq("partition", u_plus + u_minus, I2)
    assert_matrix_eq("orthogonal + -", u_plus * u_minus, Z2)
    assert_matrix_eq("orthogonal - +", u_minus * u_plus, Z2)
    assert_matrix_eq("eps split", u_plus - u_minus, eps)
    assert_matrix_eq("K square", K * K, -I2)

    for s in (-1, 0, 1):
        assert s**3 == s
        p_neg = 1 if s == -1 else 0
        p_zero = 1 if s == 0 else 0
        p_pos = 1 if s == 1 else 0
        assert p_neg + p_zero + p_pos == 1
        assert p_neg * p_neg == p_neg
        assert p_zero * p_zero == p_zero
        assert p_pos * p_pos == p_pos
    assert 0**3 == 0

    # Finite five-grade routing table.  Values are labels, not a Lie algebra model.
    def bracket_grade(a: int, b: int) -> int | str:
        if {a, b} == {-1, 1}:
            return 0
        if a == b == 1:
            return 2
        if a == b == -1:
            return -2
        if a == b == 0:
            return 0
        if a == 0 and b == 2:
            return 2
        if a == 0 and b == -2:
            return -2
        if a == b == 2:
            return "zero"
        return "unspecified"

    assert bracket_grade(-1, 1) == 0
    assert bracket_grade(1, 1) == 2
    assert bracket_grade(-1, -1) == -2
    assert bracket_grade(0, 0) == 0
    assert bracket_grade(0, 2) == 2
    assert bracket_grade(0, -2) == -2
    assert bracket_grade(2, 2) == "zero"

    print("CHIRAL_TRIPOTENT_SUPER_TKK_LEDGER_FINITE_OK")
    print("scope: finite chiral projector, tripotent classifier, and five-grade bracket-routing ledger only")


if __name__ == "__main__":
    main()
