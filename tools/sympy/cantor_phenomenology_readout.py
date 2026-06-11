#!/usr/bin/env python3
"""Finite algebra witnesses for Cantor phenomenology readouts.

The Lean module is proof authority.  This script checks small matrix/vector
models corresponding to the algebraic readouts only; it does not verify any
experimental hardware claim.
"""

from __future__ import annotations

import sympy as sp


def verify_null_projector() -> None:
    o = sp.diag(1, 0, -1)
    identity = sp.eye(3)
    p0 = identity - o**2

    assert o**3 == o
    assert p0 * p0 == p0
    assert o * p0 == sp.zeros(3)
    print("[trifactor] P0 is idempotent and O P0 = 0")


def verify_tomita_even_odd_split() -> None:
    j = sp.Matrix([[0, 1], [1, 0]])
    creation = sp.Matrix([1, 0])
    annihilation = sp.Matrix([0, 1])
    even = creation + annihilation
    odd = creation - annihilation

    assert j * creation == annihilation
    assert j * annihilation == creation
    assert j * even == even
    assert j * odd == -odd
    print("[tomita] c+a is even and c-a is odd")


def verify_chiral_trace_cancellation_sample() -> None:
    tilt = sp.diag(1, -1)
    projection = sp.eye(2)
    pairing = sp.trace(tilt * projection)

    assert pairing == 0
    print("[anomaly] finite balanced trace pairing vanishes")


def verify_braid_phase_sample() -> None:
    q = sp.symbols("q")
    v = sp.Matrix([[0, 1], [1, 0]])
    r = sp.diag(q**-4, q**3)
    lhs = sp.simplify(r * v * r)
    rhs = sp.simplify((q**-4 * q**3) * v)

    assert sp.simplify(lhs - rhs) == sp.zeros(2)
    print("[braid] R V R is a scalar phase times V")


def main() -> None:
    print("=== Cantor Phenomenology Algebraic Readout Witness ===")
    verify_null_projector()
    verify_tomita_even_odd_split()
    verify_chiral_trace_cancellation_sample()
    verify_braid_phase_sample()
    print("=== SUCCESS: algebraic readouts only ===")


if __name__ == "__main__":
    main()
