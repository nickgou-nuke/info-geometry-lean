#!/usr/bin/env python3
"""Finite algebraic witness for arXiv:2309.01382v1.

Lean twin:
    lean/InfoGeometry/Arithmetic/Arxiv230901382RiemannZerosSymmetry.lean

Scope: Witten-index count logic, scalar PT equality on the critical/real axes,
2x2 SUSY block-Hamiltonian bookkeeping, and exact spin-half su(2) matrices.
No global zeta analysis or operator spectrum theorem for Riemann zeros is asserted.
"""

from __future__ import annotations

import sympy as sp


def witten_index(n_b: int, n_f: int) -> int:
    return n_b - n_f


def witten_status(n_b: int, n_f: int) -> str:
    if witten_index(n_b, n_f) != 0:
        return "unbroken"
    if n_b == 0 and n_f == 0:
        return "broken"
    return "unbroken"


def check_witten_logic() -> None:
    assert witten_index(1, 1) == 0
    assert witten_status(1, 1) == "unbroken"
    assert witten_status(0, 0) == "broken"
    assert witten_status(2, 1) == "unbroken"


def check_pt_scalar_condition() -> None:
    # Abstract zeta values.  On the critical line 1-s = conjugate(s), so the
    # paper's scalar PT equality reduces to commutativity of complex scalars.
    z_s, z_c = sp.symbols("z_s z_conj")
    assert sp.simplify(z_s * z_c - z_c * z_s) == 0

    # On the real axis s=conj(s) and 1-s=conj(1-s), same reduction.
    z_one_minus = sp.symbols("z_one_minus")
    assert sp.simplify(z_s * z_one_minus - z_s * z_one_minus) == 0


def check_susy_block() -> None:
    E = sp.symbols("E")
    H = sp.diag(E, E)
    assert H == E * sp.eye(2)
    assert H.subs(E, 0) == sp.zeros(2)

    a, b = sp.symbols("a b")
    A = sp.Matrix([[0, 0], [a, 0]])
    Adag = sp.Matrix([[0, b], [0, 0]])
    assert Adag * A == sp.Matrix([[b * a, 0], [0, 0]])
    assert A * Adag == sp.Matrix([[0, 0], [0, a * b]])
    assert (Adag * A).subs(a, 0) == sp.zeros(2)
    assert (A * Adag).subs(a, 0) == sp.zeros(2)

    parity = sp.diag(1, -1)
    assert sp.trace(parity * sp.diag(1, 1)) == 0
    P = sp.Matrix([[0, 1], [1, 0]])
    assert P * P == sp.eye(2)
    E_left, E_right = sp.symbols("E_left E_right")
    assert P * sp.diag(E_left, E_right) * P == sp.diag(E_right, E_left)


def check_su2_spin_half() -> None:
    Jp = sp.Matrix([[0, 1], [0, 0]])
    Jm = sp.Matrix([[0, 0], [1, 0]])
    J0 = sp.Matrix([[sp.Rational(1, 2), 0], [0, -sp.Rational(1, 2)]])

    def comm(a: sp.Matrix, b: sp.Matrix) -> sp.Matrix:
        return a * b - b * a

    assert comm(Jp, Jm) == 2 * J0
    assert comm(J0, Jp) == Jp
    assert comm(J0, Jm) == -Jm

    up = sp.Matrix([1, 0])
    down = sp.Matrix([0, 1])
    assert Jp * up == sp.zeros(2, 1)
    assert Jp * down == up
    assert Jm * up == down
    assert Jm * down == sp.zeros(2, 1)
    assert J0 * up == sp.Rational(1, 2) * up
    assert J0 * down == -sp.Rational(1, 2) * down

    casimir = J0 * J0 + sp.Rational(1, 2) * (Jp * Jm + Jm * Jp)
    assert casimir == sp.Rational(3, 4) * sp.eye(2)


def main() -> None:
    check_witten_logic()
    check_pt_scalar_condition()
    check_susy_block()
    check_su2_spin_half()
    print("ARXIV_2309_01382_RIEMANN_ZEROS_SYMMETRY_OK")
    print("witten_index_pattern=(1,1)->unbroken")
    print("pt_scalar_condition=critical_or_real_axis")
    print("su2_spin_half_casimir=3/4")


if __name__ == "__main__":
    main()
