#!/usr/bin/env python3
"""Repaired Section 15: finite quaternionic Hopf checks.

This mirrors ``lean/InfoGeometry/Section15.lean``.

Closed finite checks:

* Hamilton quaternion associativity;
* conjugation involution, additivity, and multiplication reversal;
* inverse candidate qbar / |q|^2 on a concrete nonzero sample;
* norm multiplicativity for q1 * conj(q2);
* the scalar norm identity behind the quaternionic Hopf map.

Not claimed here:

* a topological fibration or fiber homeomorphism;
* S^3 as SU(2), or the double cover SU(2) -> SO(3);
* smoothness, surjectivity, or projective-space classification.
"""

from __future__ import annotations

import sys
from pathlib import Path
import sympy as sp

_REPO_ROOT = Path(__file__).resolve().parents[2]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

from tools.sympy.common import assert_zero


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


def qscale(a, q):
    return tuple(a * qi for qi in q)


def qnorm_sq(q):
    return sum(qi * qi for qi in q)


def assert_quat_equal(p, q, label: str) -> None:
    for lhs, rhs in zip(p, q):
        assert_zero(lhs - rhs, label)


def main() -> None:
    print("=" * 72)
    print("REPAIRED SECTION 15: FINITE QUATERNIONIC HOPF CHECKS")
    print("=" * 72)
    print("Scope: Hamilton algebra and Hopf norm identity.")
    print("Open debt: topology, fibers, SU(2), SO(3), and smooth fibration data.")

    a = tuple(sp.symbols("a0 a1 a2 a3", real=True))
    b = tuple(sp.symbols("b0 b1 b2 b3", real=True))
    c = tuple(sp.symbols("c0 c1 c2 c3", real=True))

    assert_quat_equal(qmul(qmul(a, b), c), qmul(a, qmul(b, c)), "quaternion associativity")
    print("  Hamilton product associativity verified")

    assert_quat_equal(qconj(qconj(a)), a, "conjugation involution")
    assert_quat_equal(qconj(qadd(a, b)), qadd(qconj(a), qconj(b)), "conjugation additivity")
    assert_quat_equal(qconj(qmul(a, b)), qmul(qconj(b), qconj(a)), "conjugation reverses multiplication")
    print("  conjugation identities verified")

    sample = (sp.Integer(1), sp.Integer(2), sp.Integer(-1), sp.Integer(3))
    sample_norm = qnorm_sq(sample)
    inv_sample = qscale(sp.Rational(1, sample_norm), qconj(sample))
    one = (sp.Integer(1), sp.Integer(0), sp.Integer(0), sp.Integer(0))
    assert_quat_equal(qmul(sample, inv_sample), one, "right inverse sample")
    assert_quat_equal(qmul(inv_sample, sample), one, "left inverse sample")
    print("  inverse candidate qbar/|q|^2 verified on a nonzero sample")

    assert_zero(qnorm_sq(qmul(a, qconj(b))) - qnorm_sq(a) * qnorm_sq(b),
                "norm multiplicativity for q1*conj(q2)")
    print("  norm multiplicativity for q1*conj(q2) verified")

    x, y = sp.symbols("x y", real=True)
    hopf_norm = (x - y) ** 2 + 4 * x * y
    assert_zero(hopf_norm - (x + y) ** 2, "Hopf scalar norm identity")
    assert_zero(hopf_norm.subs(y, 1 - x) - 1, "normalized Hopf target norm")
    print("  quaternionic Hopf S7-to-S4 norm identity verified")

    print("=" * 72)
    print("[SUCCESS] Section 15 theorem-safe finite checks verified.")
    print("=" * 72)


if __name__ == "__main__":
    main()
