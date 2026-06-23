#!/usr/bin/env python3
"""Clifford / galgebra lane for holographic tensor-factor separation."""

from __future__ import annotations

import os

import sympy as sp


os.environ.setdefault("NUMBA_DISABLE_JIT", "1")


def verify_tensor_surface() -> None:
    eta = sp.diag(1, 1, 1, 1, 1, -1, -1, -1, -1, -1)
    h1 = sp.diag(1, -1, 0)
    geom = sp.kronecker_product(eta, sp.eye(3))
    color = sp.kronecker_product(sp.eye(10), h1)
    assert geom * color == color * geom
    print("PASS: exact Kronecker tensor surface")


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
    print("PASS: clifford Cl(5,5) split geometric factor")


def verify_galgebra() -> None:
    from galgebra.ga import Ga

    ga = Ga("e1 e2 e3 e4 e5 e6 e7 e8 e9 e10", g=[1, 1, 1, 1, 1, -1, -1, -1, -1, -1])
    e = list(ga.mv_basis)
    for i in range(5):
        assert str((e[i] * e[i]).simplify()) == "1"
    for i in range(5, 10):
        assert str((e[i] * e[i]).simplify()) == "-1"
    assert str((e[0] * e[5] + e[5] * e[0]).simplify()) == "0"
    print("PASS: galgebra Cl(5,5) split geometric factor")


def main() -> None:
    print("=== Holographic tensor-factor Clifford / galgebra certificate ===")
    verify_tensor_surface()
    verify_clifford()
    verify_galgebra()
    print("HOLOGRAPHIC_TENSOR_FACTOR_SEPARATION_CLIFFORD_GALGEBRA_CERTIFICATE_OK")


if __name__ == "__main__":
    main()
