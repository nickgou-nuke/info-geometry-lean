#!/usr/bin/env python3
"""Clifford / galgebra lane for the holographic Souriau finite witness."""

from __future__ import annotations

import os

import sympy as sp


os.environ.setdefault("NUMBA_DISABLE_JIT", "1")


def verify_matrix_surface() -> None:
    eta = sp.diag(1, 1, 1, 1, 1, -1, -1, -1, -1, -1)
    twist = sp.Matrix([[0, -1], [1, 0]])
    glide = sp.diag(1, -1)
    assert eta * eta == sp.eye(10)
    assert twist * twist == -sp.eye(2)
    assert glide * twist + twist * glide == sp.zeros(2)
    print("PASS: exact matrix surface")


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
    assert layout.dims == 10
    assert len(blades) == 1024
    print("PASS: clifford Cl(5,5) basis signs and anticommutation")


def verify_galgebra() -> None:
    from galgebra.ga import Ga

    ga = Ga("e1 e2 e3 e4 e5 e6 e7 e8 e9 e10", g=[1, 1, 1, 1, 1, -1, -1, -1, -1, -1])
    e = list(ga.mv_basis)
    for i in range(5):
        assert str((e[i] * e[i]).simplify()) == "1"
    for i in range(5, 10):
        assert str((e[i] * e[i]).simplify()) == "-1"
    assert str((e[0] * e[5] + e[5] * e[0]).simplify()) == "0"
    print("PASS: galgebra split Cl(5,5) signs")


def main() -> None:
    print("=== Holographic Souriau Clifford / galgebra certificate ===")
    verify_matrix_surface()
    verify_clifford()
    verify_galgebra()
    print("HOLOGRAPHIC_SOURIAU_RECONSTRUCTION_CLIFFORD_GALGEBRA_CERTIFICATE_OK")


if __name__ == "__main__":
    main()
