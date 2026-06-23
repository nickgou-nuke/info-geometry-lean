#!/usr/bin/env python3
"""Clifford / galgebra certificate for the wallpaper/Pin(5,5) cross-section."""

from __future__ import annotations

import os

import sympy as sp


os.environ.setdefault("NUMBA_DISABLE_JIT", "1")


def verify_exact_matrix_surface() -> None:
    I5 = sp.eye(5)
    T = sp.Matrix([[0, -1], [1, 0]])
    P = sp.Matrix(
        [[0, -1, 0, 0, 0],
         [1, 0, 0, 0, 0],
         [0, 0, -1, 0, 0],
         [0, 0, 0, 1, 0],
         [0, 0, 0, 0, 1]]
    )
    eta55 = sp.diag(1, 1, 1, 1, 1, -1, -1, -1, -1, -1)
    lift = sp.diag(P, P)
    assert P.T * P == I5
    assert P[:2, :2] == T
    assert lift.T * eta55 * lift == eta55
    print("PASS: exact rational D5/O(5,5) matrix surface")


def verify_clifford() -> None:
    from clifford import Cl

    layout, blades = Cl(5, 5)
    e = [blades[f"e{i}"] for i in range(1, 11)]
    signs = [1] * 5 + [-1] * 5
    for i, ei in enumerate(e):
        assert abs(float((ei * ei)(0)) - signs[i]) < 1e-9
        for j, ej in enumerate(e):
            if i != j:
                anti = ei * ej + ej * ei
                assert max(abs(float(x)) for x in anti.value) < 1e-9

    alpha = e[0] - e[1]
    alpha_sq = float((alpha * alpha)(0))
    assert abs(alpha_sq - 2.0) < 1e-9
    v = 3 * e[0] + 7 * e[1]
    reflected = -alpha * v * (alpha / alpha_sq)
    expected = 7 * e[0] + 3 * e[1]
    assert max(abs(float(x)) for x in (reflected - expected).value) < 1e-9
    print("PASS: clifford Cl(5,5) reflection projects to wallpaper mirror")


def verify_galgebra() -> None:
    from galgebra.ga import Ga

    ga = Ga("e1 e2 e3 e4 e5 f1 f2 f3 f4 f5",
            g=[1, 1, 1, 1, 1, -1, -1, -1, -1, -1])
    e1, e2, *_ = list(ga.mv_basis)
    alpha = e1 - e2
    assert str((alpha * alpha).simplify()) == "2"
    x, y = sp.symbols("x y")
    v = x * e1 + y * e2
    reflected = (-alpha * v * (alpha / 2)).simplify()
    expected = y * e1 + x * e2
    assert (reflected - expected).simplify() == 0
    print("PASS: galgebra symbolic Pin reflection gives (x,y) -> (y,x)")


def main() -> None:
    print("=== Wallpaper / Pin(5,5) Clifford-galgebra cross-section certificate ===")
    verify_exact_matrix_surface()
    verify_clifford()
    verify_galgebra()
    print("WALLPAPER_PIN55_ROOT_CROSS_SECTION_CLIFFORD_GALGEBRA_CERTIFICATE_OK")


if __name__ == "__main__":
    main()
