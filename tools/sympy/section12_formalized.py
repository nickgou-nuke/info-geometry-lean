#!/usr/bin/env python3
"""
Corrected finite Section 12 torsion formalization -- SymPy twin.

This script mirrors lean/InfoGeometry/Section12Formalized.lean.
It verifies only the finite algebraic identities that are actually formalized:

1. vector torsion coefficients and lower-slot antisymmetry;
2. the coefficient shadow of Cartan's first structure equation;
3. coordinate-basis sign/order conventions for those coefficients;
4. spinor covariant-derivative splitting under contorsion;
5. quaternion torsion and Maurer-Cartan constant-field reductions.
"""

from __future__ import annotations

import sympy as sp

DIM = 4


def assert_zero(expr, label: str) -> None:
    reduced = sp.expand(sp.simplify(expr))
    if reduced != 0:
        raise AssertionError(f"{label} failed: {reduced}")


def qadd(p, q):
    return tuple(pi + qi for pi, qi in zip(p, q))


def qmul(p, q):
    pr, px, py, pz = p
    qr, qx, qy, qz = q
    return (
        pr * qr - px * qx - py * qy - pz * qz,
        pr * qx + px * qr + py * qz - pz * qy,
        pr * qy - px * qz + py * qr + pz * qx,
        pr * qz + px * qy - py * qx + pz * qr,
    )


def qconj(q):
    r, x, y, z = q
    return (r, -x, -y, -z)


def qdot(p, q):
    return sum(pi * qi for pi, qi in zip(p, q))


def quaternion_connection(q, dq):
    return qmul(qconj(q), dq)


def quaternion_torsion(dq, omega, q):
    return qadd(dq, qmul(omega, q))


def main() -> None:
    print("=" * 72)
    print("SECTION 12 FORMALIZED -- SYMPY VERIFICATION")
    print("=" * 72)

    gamma = {
        (a, b, c): sp.symbols(f"G_{a}_{b}_{c}")
        for a in range(DIM)
        for b in range(DIM)
        for c in range(DIM)
    }

    def torsion(gamma_table, a, b, c):
        return gamma_table[(a, b, c)] - gamma_table[(a, c, b)]

    def lower_antisym(gamma_table, a, b, c):
        return sp.Rational(1, 2) * (gamma_table[(a, b, c)] - gamma_table[(a, c, b)])

    for a in range(DIM):
        for b in range(DIM):
            for c in range(DIM):
                assert_zero(
                    torsion(gamma, a, c, b) + torsion(gamma, a, b, c),
                    "vector torsion lower-index antisymmetry",
                )
                assert_zero(
                    torsion(gamma, a, b, c) - 2 * lower_antisym(gamma, a, b, c),
                    "T = 2 Gamma_[bc]",
                )
            assert_zero(
                torsion(gamma, a, b, b),
                "repeated lower index torsion vanishes",
            )
    print("  vector torsion identities verified")

    gamma_sym = {}
    for a in range(DIM):
        for b in range(DIM):
            for c in range(DIM):
                lo, hi = sorted((b, c))
                gamma_sym[(a, b, c)] = sp.symbols(f"S_{a}_{lo}_{hi}")

    for a in range(DIM):
        for b in range(DIM):
            for c in range(DIM):
                assert_zero(
                    torsion(gamma_sym, a, b, c),
                    "symmetric lower slots imply zero torsion",
                )
    print("  torsion-free iff lower-slot symmetry sanity check passed")

    zero_connection = {(a, b, c): sp.Integer(0) for a in range(DIM) for b in range(DIM) for c in range(DIM)}

    def delta(d, c):
        return sp.Integer(1) if d == c else sp.Integer(0)

    def torsion_two_form_coeff(de_table, omega_table, frame_table, a, b, c):
        wedge_sum = sum(
            omega_table[(a, d, b)] * frame_table[(d, c)]
            - omega_table[(a, d, c)] * frame_table[(d, b)]
            for d in range(DIM)
        )
        return de_table[(a, b, c)] + wedge_sum

    frame = {(d, c): delta(d, c) for d in range(DIM) for c in range(DIM)}
    for a in range(DIM):
        for b in range(DIM):
            for c in range(DIM):
                coeff = torsion_two_form_coeff(zero_connection, gamma, frame, a, b, c)
                assert_zero(
                    coeff - (gamma[(a, c, b)] - gamma[(a, b, c)]),
                    "coordinate frame coefficient readout",
                )
                assert_zero(
                    coeff + torsion(gamma, a, b, c),
                    "coordinate frame coefficient = -torsion",
                )
                assert_zero(
                    torsion_two_form_coeff(zero_connection, gamma, frame, a, c, b)
                    - torsion(gamma, a, b, c),
                    "swapped coordinate frame coefficient = torsion",
                )
    print("  Cartan coefficient shadow and coordinate sign/order verified")

    lc00, lc01, lc10, lc11 = sp.symbols("lc00 lc01 lc10 lc11")
    k00, k01, k10, k11 = sp.symbols("k00 k01 k10 k11")
    d0, d1 = sp.symbols("d0 d1")
    p0, p1 = sp.symbols("p0 p1")

    omega_lc = sp.Matrix([[lc00, lc01], [lc10, lc11]])
    contorsion = sp.Matrix([[k00, k01], [k10, k11]])
    dpsi = sp.Matrix([[d0], [d1]])
    psi = sp.Matrix([[p0], [p1]])

    def spinor_covariant_derivative(dpsi_mat, omega_mat, psi_mat):
        return dpsi_mat + omega_mat * psi_mat

    lhs = spinor_covariant_derivative(dpsi, omega_lc + contorsion, psi)
    rhs = spinor_covariant_derivative(dpsi, omega_lc, psi) + contorsion * psi
    if sp.simplify(lhs - rhs) != sp.zeros(2, 1):
        raise AssertionError("spinor covariant derivative contorsion split failed")
    if spinor_covariant_derivative(dpsi, omega_lc + sp.zeros(2), psi) != spinor_covariant_derivative(dpsi, omega_lc, psi):
        raise AssertionError("zero contorsion reduction failed")
    if spinor_covariant_derivative(sp.zeros(2, 1), sp.zeros(2), psi) != sp.zeros(2, 1):
        raise AssertionError("flat spinor covariant derivative failed")
    print("  spinor contorsion splitting verified")

    q = tuple(sp.symbols("q0 q1 q2 q3"))
    dq = tuple(sp.symbols("dq0 dq1 dq2 dq3"))
    zero_q = (sp.Integer(0),) * 4
    one_q = (sp.Integer(1), sp.Integer(0), sp.Integer(0), sp.Integer(0))

    if quaternion_torsion(dq, zero_q, q) != dq:
        raise AssertionError("zero quaternion connection should return dq")
    if quaternion_torsion(zero_q, zero_q, q) != zero_q:
        raise AssertionError("flat quaternion torsion should vanish")

    omega = quaternion_connection(q, dq)
    assert_zero(omega[0] - qdot(q, dq), "quaternion connection real part = dot(q,dq)")

    if quaternion_connection(q, zero_q) != zero_q:
        raise AssertionError("constant-field quaternion connection should vanish")
    if quaternion_torsion(zero_q, quaternion_connection(q, zero_q), q) != zero_q:
        raise AssertionError("Maurer-Cartan torsion should vanish on constant fields")

    unit_torsion = quaternion_torsion(dq, quaternion_connection(one_q, dq), one_q)
    if unit_torsion != qadd(dq, dq):
        raise AssertionError("unit-field Maurer-Cartan torsion should be dq + dq")
    print("  quaternion torsion and Maurer-Cartan reductions verified")

    print("=" * 72)
    print("SECTION 12 FORMALIZED VERIFIED")
    print("=" * 72)


if __name__ == "__main__":
    main()
