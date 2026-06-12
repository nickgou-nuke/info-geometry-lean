#!/usr/bin/env python3
"""SymPy checks for the finite prime spinor square-root bridge.

This script mirrors the already-proved Lean identities in
`InfoGeometry.Arithmetic.PrimeSpinorSquareRootBoost`:

* `spinorBilinear_plus_minus_eq_one_sub_square`
* `projectiveRatio_chiralBoostSpinor_eq_square`
* `finiteMobiusSpinorAmplitude_sq_eq_weight_squareWeights`

The script is a witness checker only. Lean remains the proof authority.
"""

from __future__ import annotations

from functools import reduce
from operator import mul

import sympy as sp


def prod(values):
    return reduce(mul, values, sp.Integer(1))


def check_spinor_bilinear():
    a = sp.Symbol("a")
    lhs = sp.Integer(1) * sp.Integer(1) + a * (-a)
    rhs = sp.Integer(1) - a**2
    assert sp.simplify(lhs - rhs) == 0


def check_projective_ratio():
    y = sp.Symbol("y", nonzero=True)
    lhs = y * (y**-1) ** -1
    rhs = y**2
    assert sp.simplify(lhs - rhs) == 0


def check_finite_weight_square_weights():
    a1, a2, a3 = sp.symbols("a1 a2 a3")
    weights = [a1, a2, a3]
    lhs = prod(weights) ** 2
    rhs = prod([w**2 for w in weights])
    assert sp.simplify(lhs - rhs) == 0


def main() -> int:
    check_spinor_bilinear()
    check_projective_ratio()
    check_finite_weight_square_weights()
    print("prime spinor square-root checks: ok")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
