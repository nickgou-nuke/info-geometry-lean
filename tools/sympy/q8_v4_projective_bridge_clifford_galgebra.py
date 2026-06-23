#!/usr/bin/env python3
"""Clifford / galgebra witness for the finite V4 / Q8 projective bridge."""

from __future__ import annotations

import os

import sympy as sp


os.environ.setdefault("NUMBA_DISABLE_JIT", "1")


def verify_matrix_surface() -> None:
    q_i = sp.Matrix([[sp.I, 0], [0, -sp.I]])
    q_j = sp.Matrix([[0, 1], [-1, 0]])
    q_k = q_i * q_j
    assert q_i * q_i == -sp.eye(2)
    assert q_j * q_j == -sp.eye(2)
    assert q_k * q_k == -sp.eye(2)
    assert q_i * q_j == q_k
    assert q_j * q_i == -q_k
    print("PASS: exact 2x2 matrix surface")


def verify_clifford() -> None:
    from clifford import Cl

    layout, blades = Cl(3, 0)
    e1 = blades["e1"]
    e2 = blades["e2"]
    e3 = blades["e3"]
    i = -(e2 * e3)
    j = -(e3 * e1)
    k = -(e1 * e2)
    assert i * i == -1
    assert j * j == -1
    assert k * k == -1
    assert i * j == k
    assert j * i == -k
    assert j * k == i
    assert k * i == j
    print("PASS: clifford bivector quaternion witness")


def verify_galgebra() -> None:
    from galgebra.ga import Ga

    ga = Ga("e1 e2 e3", g=[1, 1, 1])
    e1, e2, e3 = ga.mv_basis
    i = -(e2 * e3)
    j = -(e3 * e1)
    k = -(e1 * e2)
    assert str((i * i).simplify()) == "-1"
    assert str((j * j).simplify()) == "-1"
    assert str((k * k).simplify()) == "-1"
    assert str((i * j - k).simplify()) == "0"
    assert str((j * i + k).simplify()) == "0"
    print("PASS: galgebra quaternionic bivector witness")


def main() -> None:
    print("=== V4 / Q8 Clifford / galgebra certificate ===")
    verify_matrix_surface()
    verify_clifford()
    verify_galgebra()
    print("Q8_V4_PROJECTIVE_BRIDGE_CLIFFORD_GALGEBRA_CERTIFICATE_OK")


if __name__ == "__main__":
    main()
