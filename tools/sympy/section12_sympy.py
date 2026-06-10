#!/usr/bin/env python3
"""
Section 12: Torsion Structure -- SymPy verification.

This script verifies the finite algebraic identities mirrored in
lean/InfoGeometry/Section12.lean.  It is deliberately not a manifold-level
Einstein-Cartan derivation; it checks the coefficient algebra used by the
formal Lean section.
"""

from __future__ import annotations

import sympy as sp


DIM = 4


def assert_zero(expr, label: str) -> None:
    reduced = sp.simplify(expr)
    if reduced != 0:
        raise AssertionError(f"{label} failed: {reduced}")


def qmul(p: tuple[sp.Expr, sp.Expr, sp.Expr, sp.Expr],
         q: tuple[sp.Expr, sp.Expr, sp.Expr, sp.Expr]) -> tuple[sp.Expr, sp.Expr, sp.Expr, sp.Expr]:
    pr, px, py, pz = p
    qr, qx, qy, qz = q
    return (
        pr * qr - px * qx - py * qy - pz * qz,
        pr * qx + px * qr + py * qz - pz * qy,
        pr * qy - px * qz + py * qr + pz * qx,
        pr * qz + px * qy - py * qx + pz * qr,
    )


def qadd(p: tuple[sp.Expr, sp.Expr, sp.Expr, sp.Expr],
         q: tuple[sp.Expr, sp.Expr, sp.Expr, sp.Expr]) -> tuple[sp.Expr, sp.Expr, sp.Expr, sp.Expr]:
    return tuple(pi + qi for pi, qi in zip(p, q))


def qconj(q: tuple[sp.Expr, sp.Expr, sp.Expr, sp.Expr]) -> tuple[sp.Expr, sp.Expr, sp.Expr, sp.Expr]:
    r, x, y, z = q
    return (r, -x, -y, -z)


def quaternion_torsion(dq, omega, q):
    return qadd(dq, qmul(omega, q))


def main() -> None:
    print("=" * 72)
    print("SECTION 12: TORSION STRUCTURE -- SYMPY VERIFICATION")
    print("=" * 72)

    # 12.1 Vector torsion T^a_bc = Gamma^a_bc - Gamma^a_cb.
    gamma = {
        (a, b, c): sp.symbols(f"G_{a}_{b}_{c}")
        for a in range(DIM) for b in range(DIM) for c in range(DIM)
    }

    def torsion(gamma_table, a, b, c):
        return gamma_table[(a, b, c)] - gamma_table[(a, c, b)]

    for a in range(DIM):
        for b in range(DIM):
            for c in range(DIM):
                assert_zero(
                    torsion(gamma, a, c, b) + torsion(gamma, a, b, c),
                    "torsion lower-index antisymmetry",
                )
                lower_antisym = sp.Rational(1, 2) * (
                    gamma[(a, b, c)] - gamma[(a, c, b)]
                )
                assert_zero(
                    torsion(gamma, a, b, c) - 2 * lower_antisym,
                    "T = 2 Gamma_[bc]",
                )
    print("  vector torsion antisymmetry and T = 2*Gamma_[bc] verified")

    gamma_sym = {}
    for a in range(DIM):
        for b in range(DIM):
            for c in range(DIM):
                lo, hi = sorted((b, c))
                gamma_sym[(a, b, c)] = sp.symbols(f"S_{a}_{lo}_{hi}")

    for a in range(DIM):
        for b in range(DIM):
            for c in range(DIM):
                assert_zero(torsion(gamma_sym, a, b, c), "symmetric connection torsion")
    print("  lower-index symmetric connection is torsion-free")

    # 12.1 Cartan first structure equation in coefficients:
    # T^a_bc = de^a_bc + sum_d (omega^a_db e^d_c - omega^a_dc e^d_b).
    de_seed = {
        (a, min(b, c), max(b, c)): sp.symbols(f"de_{a}_{min(b, c)}_{max(b, c)}")
        for a in range(DIM) for b in range(DIM) for c in range(DIM) if b != c
    }

    def de(a, b, c):
        if b == c:
            return sp.Integer(0)
        lo, hi = sorted((b, c))
        value = de_seed[(a, lo, hi)]
        return value if b < c else -value

    omega = {
        (a, d, b): sp.symbols(f"w_{a}_{d}_{b}")
        for a in range(DIM) for d in range(DIM) for b in range(DIM)
    }
    frame = {
        (d, b): sp.symbols(f"e_{d}_{b}")
        for d in range(DIM) for b in range(DIM)
    }

    def torsion_two_form_coeff(a, b, c):
        wedge_sum = sum(
            omega[(a, d, b)] * frame[(d, c)] - omega[(a, d, c)] * frame[(d, b)]
            for d in range(DIM)
        )
        return de(a, b, c) + wedge_sum

    for a in range(DIM):
        for b in range(DIM):
            for c in range(DIM):
                assert_zero(
                    torsion_two_form_coeff(a, c, b) + torsion_two_form_coeff(a, b, c),
                    "Cartan torsion two-form coefficient antisymmetry",
                )
    print("  Cartan torsion two-form coefficient antisymmetry verified")

    # 12.2 Spinorial channel: torsion appears as contorsion added to omega.
    omega_lc = sp.Matrix([[sp.symbols("lc00"), sp.symbols("lc01")],
                          [sp.symbols("lc10"), sp.symbols("lc11")]])
    contorsion = sp.zeros(2)
    omega_total = omega_lc + contorsion
    if omega_total != omega_lc:
        raise AssertionError("zero contorsion should reduce to Levi-Civita spin connection")
    if sp.zeros(2) + sp.zeros(2) != sp.zeros(2):
        raise AssertionError("flat spin connection check failed")
    print("  zero-contorsion and flat spin-connection reductions verified")

    # 12.3 Quaternion torsion T_q = dq + Omega*q.
    q = tuple(sp.symbols("q0 q1 q2 q3"))
    dq = tuple(sp.symbols("dq0 dq1 dq2 dq3"))
    zero_q = (sp.Integer(0),) * 4

    flat_torsion = quaternion_torsion(zero_q, zero_q, q)
    if flat_torsion != zero_q:
        raise AssertionError(f"flat quaternion torsion failed: {flat_torsion}")

    zero_connection_torsion = quaternion_torsion(dq, zero_q, q)
    if zero_connection_torsion != dq:
        raise AssertionError("zero quaternion connection should return dq")

    constant_connection = qmul(qconj(q), zero_q)
    if constant_connection != zero_q:
        raise AssertionError("qbar*dq should vanish for dq=0")

    constant_field_torsion = quaternion_torsion(zero_q, constant_connection, q)
    if constant_field_torsion != zero_q:
        raise AssertionError("constant-field quaternion torsion should vanish")
    print("  quaternion torsion flat and zero-connection reductions verified")

    print("=" * 72)
    print("SECTION 12 VERIFIED")
    print("=" * 72)


if __name__ == "__main__":
    main()
