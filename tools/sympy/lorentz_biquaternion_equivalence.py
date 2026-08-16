#!/usr/bin/env python3
"""Finite Lorentz/biquaternion equivalence witness.

Closed finite content only:
- Pauli/Hermitian spacetime matrix determinant equals the Minkowski quadratic form;
- an exact determinant-one real 2×2 matrix acts by double-sided transport and
  preserves that determinant;
- the central sign ±I acts trivially on the transported Hermitian matrix;
- the corresponding Clifford/galgebra boost bivector squares to +1 in signature
  (1,3), matching the hyperbolic Lorentz-boost generator lane.

Not claimed:
- a full formal proof that Spin(1,3) ≃ SL(2,C),
- a global Lie-group isomorphism theorem,
- analytic exponential/rapidity classification,
- arbitrary categorical or physical unification claims.
"""

from __future__ import annotations

import sys
from pathlib import Path
import sympy as sp
from clifford import Cl
from galgebra.ga import Ga

_REPO_ROOT = Path(__file__).resolve().parents[2]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

from tools.sympy.common import assert_matrix_zero, assert_zero, pauli_matrices


def hermitian_spacetime(t: sp.Expr, x: sp.Expr, y: sp.Expr, z: sp.Expr) -> sp.Matrix:
    I2, sigma1, sigma2, sigma3 = pauli_matrices()
    return t * I2 + x * sigma1 + y * sigma2 + z * sigma3


def exact_boost_q() -> sp.Matrix:
    # Exact determinant-one real matrix. Since Q† = Q here, the transport lane is
    # X ↦ Q X Q, a theorem-safe exact slice of the SL(2,C)/Hermitian action.
    return sp.Matrix([[2, 1], [1, 1]])


def verify_sympy_lane() -> None:
    t, x, y, z = sp.symbols("t x y z")
    X = hermitian_spacetime(t, x, y, z)
    minkowski = t**2 - x**2 - y**2 - z**2
    assert_zero(X.det() - minkowski, "Pauli/Hermitian determinant readout")

    Q = exact_boost_q()
    assert_zero(Q.det() - 1, "exact boost determinant one")
    Xp = Q * X * Q
    assert_zero(Xp.det() - X.det(), "double-sided determinant preservation")

    minus_I = -sp.eye(2)
    assert_matrix_zero(minus_I * X * minus_I - X, "central sign acts trivially")
    assert_zero(((-Q) * X * (-Q)).det() - X.det(), "sign-changed transport preserves determinant")

    print("sympy: determinant readout, exact boost transport, and Z2 sign kernel: OK")


def verify_clifford_lane() -> None:
    layout, blades = Cl(1, 3, names="e")
    # In this API, e1^2=+1 and e2^2=e3^2=e4^2=-1.
    e1 = blades["e1"]
    e2 = blades["e2"]
    boost_bivector = e1 * e2
    if boost_bivector * boost_bivector != 1:
        raise AssertionError(f"clifford boost bivector square failed: {boost_bivector * boost_bivector}")
    print("clifford: boost bivector square in Cl(1,3): OK")


def verify_galgebra_lane() -> None:
    st4 = Ga("e0 e1 e2 e3", g=[1, -1, -1, -1])
    e0, e1, _e2, _e3 = st4.mv()
    boost_bivector = e0 ^ e1
    square = sp.simplify((boost_bivector * boost_bivector).scalar())
    if square != 1:
        raise AssertionError(f"galgebra boost bivector square failed: {square}")
    print("galgebra: boost bivector square in signature (1,3): OK")


def main() -> int:
    print("=" * 72)
    print("LORENTZ / BIQUATERNION EQUIVALENCE — FINITE EXACT WITNESS")
    print("=" * 72)
    verify_sympy_lane()
    verify_clifford_lane()
    verify_galgebra_lane()
    print("=" * 72)
    print("LORENTZ / BIQUATERNION FINITE WITNESS VERIFIED")
    print("=" * 72)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
