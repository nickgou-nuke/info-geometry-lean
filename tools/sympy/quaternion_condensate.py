#!/usr/bin/env python3
"""
Finite quaternion condensate verification.

Mirrors lean/InfoGeometry/Canonical/QuaternionCondensate.lean.
This is coefficient algebra only: no electromagnetic field, no Clifford
embedding theorem, and no Einstein-Cartan dynamics are claimed here.
"""

from __future__ import annotations

import sympy as sp


def qadd(p, q):
    return tuple(a + b for a, b in zip(p, q))


def qneg(q):
    return tuple(-a for a in q)


def qmul(p, q):
    pr, pi, pj, pk = p
    qr, qi, qj, qk = q
    return (
        pr * qr - pi * qi - pj * qj - pk * qk,
        pr * qi + pi * qr + pj * qk - pk * qj,
        pr * qj - pi * qk + pj * qr + pk * qi,
        pr * qk + pi * qj - pj * qi + pk * qr,
    )


def qconj(q):
    r, i, j, k = q
    return (r, -i, -j, -k)


def norm_sq(q):
    return sum(x * x for x in q)


def real_part(q):
    return q[0]


def assert_quat_eq(p, q, label: str):
    diff = tuple(sp.expand(sp.simplify(a - b)) for a, b in zip(p, q))
    if any(d != 0 for d in diff):
        raise AssertionError(f"{label} failed: {diff}")


def assert_zero(expr, label: str):
    reduced = sp.expand(sp.simplify(expr))
    if reduced != 0:
        raise AssertionError(f"{label} failed: {reduced}")


def main() -> None:
    print("=" * 72)
    print("QUATERNION CONDENSATE -- FINITE SYMPY VERIFICATION")
    print("=" * 72)

    one = (sp.Integer(1), 0, 0, 0)
    qi = (0, sp.Integer(1), 0, 0)
    qj = (0, 0, sp.Integer(1), 0)
    qk = (0, 0, 0, sp.Integer(1))

    assert_quat_eq(qmul(qi, qi), qneg(one), "i^2 = -1")
    assert_quat_eq(qmul(qj, qj), qneg(one), "j^2 = -1")
    assert_quat_eq(qmul(qk, qk), qneg(one), "k^2 = -1")
    assert_quat_eq(qmul(qi, qj), qk, "ij = k")
    assert_quat_eq(qmul(qj, qk), qi, "jk = i")
    assert_quat_eq(qmul(qk, qi), qj, "ki = j")
    assert_quat_eq(qmul(qj, qi), qneg(qk), "ji = -k")
    assert_quat_eq(qmul(qmul(qi, qj), qk), qneg(one), "ijk = -1")
    print("  quaternion basis laws verified")

    a, b, c, d = sp.symbols("a b c d", real=True)
    e, f, g, h = sp.symbols("e f g h", real=True)
    p = (a, b, c, d)
    q = (e, f, g, h)

    assert_quat_eq(qmul(p, qconj(p)), (norm_sq(p), 0, 0, 0), "q*qbar = norm")
    assert_quat_eq(qmul(qconj(p), p), (norm_sq(p), 0, 0, 0), "qbar*q = norm")
    assert_zero(norm_sq(qmul(p, q)) - norm_sq(p) * norm_sq(q), "multiplicative norm")
    print("  conjugation and norm laws verified")

    u, v = sp.symbols("u v", real=True)
    phase = (u, v, 0, 0)
    rotated = qmul(phase, p)
    assert_zero(norm_sq(rotated) - (u * u + v * v) * norm_sq(p), "phase norm scaling")
    assert_zero(
        (norm_sq(rotated) - norm_sq(p)) - (u * u + v * v - 1) * norm_sq(p),
        "unit phase metric invariance",
    )
    inverse_rotated = qmul((u, -v, 0, 0), rotated)
    inverse_defect = qadd(inverse_rotated, qneg(p))
    expected_inverse_defect = tuple((u * u + v * v - 1) * component for component in p)
    assert_quat_eq(inverse_defect, expected_inverse_defect, "unit phase inverse closure")
    print("  U(1)-style unit phase norm/metric invariance and inverse closure verified")

    comm_pq = qadd(qmul(p, q), qneg(qmul(q, p)))
    comm_qp = qadd(qmul(q, p), qneg(qmul(p, q)))
    assert_quat_eq(comm_qp, qneg(comm_pq), "commutator antisymmetry")

    x0, x1, x2, x3 = sp.symbols("x0 x1 x2 x3", real=True)
    axis = (x0, x1, x2, x3)
    torsion = real_part(qmul(qconj(p), qmul(axis, comm_pq)))
    torsion_swapped = real_part(qmul(qconj(p), qmul(axis, comm_qp)))
    assert_zero(torsion_swapped + torsion, "torsion readout antisymmetry")
    print("  commutator and torsion-readout antisymmetry verified")

    eta00, eta01, eta11 = sp.symbols("eta00 eta01 eta11", real=True)
    eta = sp.Matrix([[eta00, eta01], [eta01, eta11]])
    emu0, emu1, enu0, enu1 = sp.symbols("emu0 emu1 enu0 enu1", real=True)
    emu = sp.Matrix([emu0, emu1])
    enu = sp.Matrix([enu0, enu1])
    g_mn = (emu.T * eta * enu)[0]
    g_nm = (enu.T * eta * emu)[0]
    assert_zero(g_mn - g_nm, "finite induced metric symmetry")
    print("  finite induced metric symmetry verified")

    print("=" * 72)
    print("QUATERNION CONDENSATE VERIFIED")
    print("=" * 72)


if __name__ == "__main__":
    main()
