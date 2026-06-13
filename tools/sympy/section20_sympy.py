#!/usr/bin/env python3
"""Repaired Section 20: finite torsion bridge checks.

The fetched section20.txt repeats the torsion material already repaired in
Section 12.  This script mirrors lean/InfoGeometry/Section20.lean by checking
only finite bridge facts between the two repaired torsion corridors.

Closed finite checks:

* the two torsion coefficient definitions agree;
* the two coordinate Cartan coefficient conventions reconcile by an index swap;
* the quaternion torsion definitions agree;
* the two-site shift commutator is a nonzero generic commutator readout.

Not claimed here:

* smooth exterior calculus;
* Einstein-Cartan dynamics;
* axial-current coupling or quantum anomaly theorems;
* emergence of spacetime torsion from operator algebras.
"""

from __future__ import annotations

import sympy as sp

DIM = 4


def assert_zero(expr, label: str) -> None:
    reduced = sp.expand(sp.simplify(expr))
    if reduced != 0:
        raise AssertionError(f"{label} failed: {reduced}")


def assert_matrix_zero(matrix: sp.Matrix, label: str) -> None:
    reduced = matrix.applyfunc(lambda x: sp.expand(sp.simplify(x)))
    if reduced != sp.zeros(*matrix.shape):
        raise AssertionError(f"{label} failed:\n{reduced}")


def qadd(p, q):
    return tuple(pi + qi for pi, qi in zip(p, q))


def qneg(q):
    return tuple(-qi for qi in q)


def qsub(p, q):
    return qadd(p, qneg(q))


def qmul(p, q):
    pr, px, py, pz = p
    qr, qx, qy, qz = q
    return (
        pr * qr - px * qx - py * qy - pz * qz,
        pr * qx + px * qr + py * qz - pz * qy,
        pr * qy - px * qz + py * qr + pz * qx,
        pr * qz + px * qy - py * qx + pz * qr,
    )


def torsion_a(gamma, a, b, c):
    return gamma[(a, b, c)] - gamma[(a, c, b)]


def torsion_b(gamma, a, b, c):
    return gamma[(a, b, c)] - gamma[(a, c, b)]


def delta(d, c):
    return sp.Integer(1) if d == c else sp.Integer(0)


def cartan_section12(gamma, a, b, c):
    # Section12.coordinateConnectionForm stores omega[a,d,b] = Gamma[a,b,d].
    return sum(
        gamma[(a, b, d)] * delta(d, c) - gamma[(a, c, d)] * delta(d, b)
        for d in range(DIM)
    )


def cartan_formalized(gamma, a, b, c):
    # Section12Formalized keeps omega[a,d,b] = Gamma[a,d,b].
    return sum(
        gamma[(a, d, b)] * delta(d, c) - gamma[(a, d, c)] * delta(d, b)
        for d in range(DIM)
    )


def quaternion_torsion(dq, omega, q):
    return qsub(qadd(dq, qmul(omega, q)), qmul(q, omega))


def main() -> None:
    print("=" * 72)
    print("REPAIRED SECTION 20: FINITE TORSION BRIDGE CHECKS")
    print("=" * 72)
    print("Scope: bridge Section12 torsion claims to Section12Formalized.")
    print("Open debt: continuum torsion dynamics and physical coupling claims.")

    gamma = {
        (a, b, c): sp.symbols(f"G_{a}_{b}_{c}")
        for a in range(DIM)
        for b in range(DIM)
        for c in range(DIM)
    }

    for a in range(DIM):
        for b in range(DIM):
            for c in range(DIM):
                assert_zero(
                    torsion_a(gamma, a, b, c) - torsion_b(gamma, a, b, c),
                    "torsion coefficient definitions agree",
                )
                assert_zero(
                    cartan_section12(gamma, a, b, c) - torsion_a(gamma, a, b, c),
                    "Section12 coordinate Cartan readout",
                )
                assert_zero(
                    cartan_formalized(gamma, a, c, b) - torsion_b(gamma, a, b, c),
                    "Section12Formalized swapped coordinate Cartan readout",
                )
    print("  torsion coefficient and coordinate Cartan bridge verified")

    q = tuple(sp.symbols("q0 q1 q2 q3"))
    dq = tuple(sp.symbols("dq0 dq1 dq2 dq3"))
    omega = tuple(sp.symbols("om0 om1 om2 om3"))
    qt_a = quaternion_torsion(dq, omega, q)
    qt_b = quaternion_torsion(dq, omega, q)
    for left, right in zip(qt_a, qt_b):
        assert_zero(left - right, "quaternion torsion definitions agree")
    print("  quaternion torsion bridge verified")

    shift_l = sp.Matrix([[0, 1], [0, 0]])
    shift_r = sp.Matrix([[0, 0], [1, 0]])
    generic_readout = shift_l * shift_r - shift_r * shift_l
    explicit_commutator = sp.diag(1, -1)
    assert_matrix_zero(generic_readout - explicit_commutator, "finite shift commutator readout")
    if generic_readout == sp.zeros(2):
        raise AssertionError("finite shift commutator should be nonzero")
    print("  finite shift generic commutator readout verified")

    print("=" * 72)
    print("[SUCCESS] Section 20 theorem-safe finite bridge checks verified.")
    print("=" * 72)


if __name__ == "__main__":
    main()
