#!/usr/bin/env python3
"""
Section 12: Torsion Structure -- SymPy verification.

This script verifies the finite algebraic identities mirrored in
lean/InfoGeometry/Canonical/TorsionStructure.lean.  It is deliberately not a manifold-level
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


def qneg(q: tuple[sp.Expr, sp.Expr, sp.Expr, sp.Expr]) -> tuple[sp.Expr, sp.Expr, sp.Expr, sp.Expr]:
    return tuple(-qi for qi in q)


def qsub(p: tuple[sp.Expr, sp.Expr, sp.Expr, sp.Expr],
         q: tuple[sp.Expr, sp.Expr, sp.Expr, sp.Expr]) -> tuple[sp.Expr, sp.Expr, sp.Expr, sp.Expr]:
    return qadd(p, qneg(q))


def qconj(q: tuple[sp.Expr, sp.Expr, sp.Expr, sp.Expr]) -> tuple[sp.Expr, sp.Expr, sp.Expr, sp.Expr]:
    r, x, y, z = q
    return (r, -x, -y, -z)


def quaternion_torsion(dq, omega, q):
    return qadd(dq, qsub(qmul(omega, q), qmul(q, omega)))


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

    def coordinate_frame(d, c):
        return sp.Integer(1) if d == c else sp.Integer(0)

    def coordinate_connection_form(gamma_table, a, d, b):
        # omega^a_d = Gamma^a_{bd} dx^b
        return gamma_table[(a, b, d)]

    def coordinate_torsion_two_form_coeff(gamma_table, a, b, c):
        wedge_sum = sum(
            coordinate_connection_form(gamma_table, a, d, b) * coordinate_frame(d, c)
            - coordinate_connection_form(gamma_table, a, d, c) * coordinate_frame(d, b)
            for d in range(DIM)
        )
        return wedge_sum

    for a in range(DIM):
        for b in range(DIM):
            for c in range(DIM):
                assert_zero(
                    coordinate_torsion_two_form_coeff(gamma, a, b, c)
                    - torsion(gamma, a, b, c),
                    "coordinate Cartan torsion reduction",
                )
    print("  coordinate Cartan reduction to T^a_bc = Gamma^a_bc - Gamma^a_cb verified")

    # 12.2 Spinorial channel: torsion appears as contorsion added to omega.
    torsion_lower = {
        (a, b, c): sp.symbols(f"T_{a}_{b}_{c}")
        for a in range(DIM) for b in range(DIM) for c in range(DIM)
    }

    def contorsion_from_torsion(torsion_table, a, b, c):
        return sp.Rational(1, 2) * (
            torsion_table[(a, b, c)]
            + torsion_table[(c, a, b)]
            - torsion_table[(b, c, a)]
        )

    zero_torsion_lower = {
        (a, b, c): sp.Integer(0)
        for a in range(DIM) for b in range(DIM) for c in range(DIM)
    }
    for a in range(DIM):
        for b in range(DIM):
            for c in range(DIM):
                assert_zero(
                    contorsion_from_torsion(zero_torsion_lower, a, b, c),
                    "zero torsion gives zero contorsion",
                )
                expected = sp.Rational(1, 2) * (
                    torsion_lower[(a, b, c)]
                    + torsion_lower[(c, a, b)]
                    - torsion_lower[(b, c, a)]
                )
                assert_zero(
                    contorsion_from_torsion(torsion_lower, a, b, c) - expected,
                    "contorsion formula",
                )
    print("  contorsion K_abc = 1/2(T_abc + T_cab - T_bca) verified")

    omega_lc = sp.Matrix([[sp.symbols("lc00"), sp.symbols("lc01")],
                          [sp.symbols("lc10"), sp.symbols("lc11")]])
    contorsion = sp.zeros(2)
    omega_total = omega_lc + contorsion
    if omega_total != omega_lc:
        raise AssertionError("zero contorsion should reduce to Levi-Civita spin connection")
    if sp.zeros(2) + sp.zeros(2) != sp.zeros(2):
        raise AssertionError("flat spin connection check failed")

    omega_spin = sp.Matrix([[sp.symbols("w00"), sp.symbols("w01")],
                            [sp.symbols("w10"), sp.symbols("w11")]])
    soldering = sp.Matrix([[sp.symbols("e00"), sp.symbols("e01")],
                           [sp.symbols("e10"), sp.symbols("e11")]])

    def matrix_commutator(a, b):
        return a * b - b * a

    def clifford_soldering_derivative(de_matrix, omega_matrix, soldering_matrix):
        return de_matrix + matrix_commutator(omega_matrix, soldering_matrix)

    flat_soldering = clifford_soldering_derivative(sp.zeros(2), sp.zeros(2), soldering)
    if flat_soldering != sp.zeros(2):
        raise AssertionError("flat Clifford soldering derivative should vanish")
    if clifford_soldering_derivative(sp.zeros(2), omega_spin, sp.eye(2)) != sp.zeros(2):
        raise AssertionError("identity soldering should commute with any spin connection")
    print("  zero-contorsion, flat spin, and Clifford-soldering commutator checks verified")

    # 12.3 Quaternion torsion T_q = dq + Omega*q - q*Omega.
    q = tuple(sp.symbols("q0 q1 q2 q3"))
    dq = tuple(sp.symbols("dq0 dq1 dq2 dq3"))
    omega_q = tuple(sp.symbols("om0 om1 om2 om3"))
    zero_q = (sp.Integer(0),) * 4

    flat_torsion = quaternion_torsion(zero_q, zero_q, q)
    if flat_torsion != zero_q:
        raise AssertionError(f"flat quaternion torsion failed: {flat_torsion}")

    zero_connection_torsion = quaternion_torsion(dq, zero_q, q)
    if zero_connection_torsion != dq:
        raise AssertionError("zero quaternion connection should return dq")

    commutator_torsion = quaternion_torsion(zero_q, omega_q, q)
    expected_commutator = qsub(qmul(omega_q, q), qmul(q, omega_q))
    if any(sp.simplify(a - b) != 0 for a, b in zip(commutator_torsion, expected_commutator)):
        raise AssertionError("quaternion torsion should use the commutator action")

    constant_connection = qmul(qconj(q), zero_q)
    if constant_connection != zero_q:
        raise AssertionError("qbar*dq should vanish for dq=0")

    constant_field_torsion = quaternion_torsion(zero_q, constant_connection, q)
    if constant_field_torsion != zero_q:
        raise AssertionError("constant-field quaternion torsion should vanish")

    deq_seed = {
        (min(mu, nu), max(mu, nu), comp): sp.symbols(f"deq_{min(mu, nu)}_{max(mu, nu)}_{comp}")
        for mu in range(DIM) for nu in range(DIM) if mu != nu for comp in range(4)
    }

    def deq(mu, nu):
        if mu == nu:
            return zero_q
        lo, hi = sorted((mu, nu))
        value = tuple(deq_seed[(lo, hi, comp)] for comp in range(4))
        return value if mu < nu else qneg(value)

    omega_form = {
        mu: tuple(sp.symbols(f"O_{mu}_{comp}") for comp in range(4))
        for mu in range(DIM)
    }
    solder_form = {
        mu: tuple(sp.symbols(f"E_{mu}_{comp}") for comp in range(4))
        for mu in range(DIM)
    }

    def quaternion_torsion_two_form_coeff(mu, nu):
        return qadd(
            qadd(deq(mu, nu), qsub(qmul(omega_form[mu], solder_form[nu]),
                                  qmul(omega_form[nu], solder_form[mu]))),
            qsub(qmul(solder_form[mu], qconj(omega_form[nu])),
                 qmul(solder_form[nu], qconj(omega_form[mu]))),
        )

    for mu in range(DIM):
        for nu in range(DIM):
            lhs = quaternion_torsion_two_form_coeff(nu, mu)
            rhs = qneg(quaternion_torsion_two_form_coeff(mu, nu))
            if any(sp.simplify(a - b) != 0 for a, b in zip(lhs, rhs)):
                raise AssertionError("quaternion two-form coefficient antisymmetry failed")
    print("  quaternion torsion commutator and conjugate-wedge checks verified")

    # 12.4 Finite noncommutative shift witness.
    shift_l = sp.Matrix([[0, 1], [0, 0]])
    shift_r = sp.Matrix([[0, 0], [1, 0]])
    shift_commutator = shift_l * shift_r - shift_r * shift_l
    expected_shift_commutator = sp.Matrix([[1, 0], [0, -1]])
    if shift_commutator != expected_shift_commutator:
        raise AssertionError(f"finite shift commutator mismatch: {shift_commutator}")
    if shift_commutator == sp.zeros(2):
        raise AssertionError("finite shift commutator should be nonzero")
    print("  finite noncommuting shift witness verified")

    print("=" * 72)
    print("SECTION 12 VERIFIED")
    print("=" * 72)


if __name__ == "__main__":
    main()
