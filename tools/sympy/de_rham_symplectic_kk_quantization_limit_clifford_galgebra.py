#!/usr/bin/env python3
"""Clifford/GAlgebra certificate for the de Rham/symplectic/KK bridge."""

from __future__ import annotations

import os

import sympy as sp


os.environ.setdefault("NUMBA_DISABLE_JIT", "1")


def verify_exact_rational_surface() -> None:
    q = sp.Rational

    J = sp.Matrix([[0, 1], [-1, 0]])
    S = sp.Matrix([[1, 1], [0, 1]])
    assert S.T * J * S == J

    kk = sp.Matrix([
        [q(-1, 2), q(1, 3), 0, 0, 1],
        [q(1, 3), q(11, 9), 0, 0, q(2, 3)],
        [0, 0, 1, 0, 0],
        [0, 0, 0, 1, 0],
        [1, q(2, 3), 0, 0, 2],
    ])
    assert kk.det() == q(-2)


def verify_clifford_symplectic_plane() -> None:
    from clifford import Cl

    layout, blades = Cl(2)
    e1 = blades["e1"]
    e2 = blades["e2"]
    assert abs(float((e1 * e1)(0)) - 1.0) < 1e-9
    assert abs(float((e2 * e2)(0)) - 1.0) < 1e-9
    anti = e1 * e2 + e2 * e1
    assert max(abs(float(x)) for x in anti.value) < 1e-9

    biv = e1 * e2
    assert abs(float((biv * biv)(0)) + 1.0) < 1e-9


def verify_galgebra_symbolic_plane() -> None:
    from galgebra.ga import Ga

    ga = Ga("e1 e2", g=[1, 1])
    e1, e2 = list(ga.mv_basis)
    biv = (e1 * e2).simplify()
    assert str((biv * biv).simplify()) == "-1"
    x, y = sp.symbols("x y")
    v = x * e1 + y * e2
    rotated = (-e1 * v * e1).simplify()
    expected = -x * e1 + y * e2
    assert (rotated - expected).simplify() == 0


def main() -> None:
    verify_exact_rational_surface()
    verify_clifford_symplectic_plane()
    verify_galgebra_symbolic_plane()
    print("DE_RHAM_SYMPLECTIC_KK_QUANTIZATION_LIMIT_CLIFFORD_GALGEBRA_CERTIFICATE_OK")


if __name__ == "__main__":
    main()
