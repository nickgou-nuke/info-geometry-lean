#!/usr/bin/env python3
"""Clifford / galgebra certificate for the holographic Cuntz shard algebra."""

from __future__ import annotations

import os

import sympy as sp


os.environ.setdefault("NUMBA_DISABLE_JIT", "1")


def verify_exact_matrix_surface() -> None:
    S = sp.Matrix([[0, 1], [0, 0]])
    T = sp.Matrix([[0, 0], [1, 0]])
    p = sp.Matrix([[0, 0], [0, 1]])
    q = sp.Matrix([[1, 0], [0, 0]])
    assert S.T * S == p
    assert S * S.T == q
    assert T.T * T == q
    assert p * p == p
    assert q * q == q
    assert p + q == sp.eye(2)
    assert S * S.T * S == S
    print("PASS: exact rational finite shard matrix identities")


def verify_clifford() -> None:
    from clifford import Cl

    _layout, blades = Cl(1, 1)
    e1 = blades["e1"]
    e2 = blades["e2"]
    u = (e1 + e2) / 2
    v = (e1 - e2) / 2
    p = u * v
    q = v * u
    one = blades[""]

    def close_zero(mv) -> bool:
        return max(abs(float(c)) for c in mv.value) < 1e-9

    assert close_zero(u * u)
    assert close_zero(v * v)
    assert close_zero(p * p - p)
    assert close_zero(q * q - q)
    assert close_zero(p + q - one)
    assert close_zero(u * v * u - u)
    print("PASS: clifford Cl(1,1) null shard projectors")


def verify_galgebra() -> None:
    from galgebra.ga import Ga

    ga = Ga("e f", g=[1, -1])
    e, f = list(ga.mv_basis)
    u = (e + f) / 2
    v = (e - f) / 2
    p = (u * v).simplify()
    q = (v * u).simplify()
    assert (u * u).simplify() == 0
    assert (v * v).simplify() == 0
    assert (p * p - p).simplify() == 0
    assert (q * q - q).simplify() == 0
    assert (p + q - 1).simplify() == 0
    assert (u * v * u - u).simplify() == 0
    print("PASS: galgebra exact null shard projector algebra")


def main() -> None:
    print("=== Holographic Cuntz shard Clifford/GAlgebra certificate ===")
    verify_exact_matrix_surface()
    verify_clifford()
    verify_galgebra()
    print("HOLOGRAPHIC_CUNTZ_SHARD_CLIFFORD_GALGEBRA_CERTIFICATE_OK")


if __name__ == "__main__":
    main()
