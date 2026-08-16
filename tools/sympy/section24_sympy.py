#!/usr/bin/env python3
"""Repaired Section 24: finite quaternionic extension checks.

This mirrors ``lean/InfoGeometry/Section24.lean`` and checks the advertised
gamma-bivector quaternion model directly.

Closed finite checks:

* gamma bivectors ``gamma1*gamma2``, ``gamma2*gamma3``, ``gamma3*gamma1``
  satisfy the Hamilton multiplication table;
* the source's ``ijk`` line is repaired to the scalar matrix ``-I``;
* quaternion conjugation gives norm squared;
* quaternion-induced metric coefficients are symmetric;
* torsion built from a finite commutator difference is antisymmetric.

Not claimed here: condensate existence, smooth covariant derivatives, operator
reality from adjoints, curvature decomposition, inverse-vielbein equations, or
the proposed gravitational bootstrap.
"""

from __future__ import annotations

import sys
from pathlib import Path
import sympy as sp

_REPO_ROOT = Path(__file__).resolve().parents[2]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

from tools.sympy.common import assert_matrix_zero, assert_zero


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


def qnorm_sq(q):
    return sum(component**2 for component in q)


def main() -> None:
    print("=" * 72)
    print("REPAIRED SECTION 24: FINITE QUATERNIONIC EXTENSION CORE")
    print("=" * 72)
    print("Scope: finite quaternion algebra, metric symmetry, commutator antisymmetry.")
    print("Open debt: condensates, field equations, curvature formulas, bootstrap loop.")

    I = sp.I
    I2 = sp.eye(2)
    I4 = sp.eye(4)
    sigma1 = sp.Matrix([[0, 1], [1, 0]])
    sigma2 = sp.Matrix([[0, -I], [I, 0]])
    sigma3 = sp.Matrix([[1, 0], [0, -1]])
    tau3 = sp.Matrix([[1, 0], [0, -1]])
    epsilon = sp.Matrix([[0, 1], [-1, 0]])

    gamma0 = sp.kronecker_product(tau3, I2)
    gamma1 = sp.kronecker_product(epsilon, sigma1)
    gamma2 = sp.kronecker_product(epsilon, sigma2)
    gamma3 = sp.kronecker_product(epsilon, sigma3)
    _ = gamma0

    qi = gamma1 * gamma2
    qj = gamma2 * gamma3
    qk = gamma3 * gamma1

    assert_matrix_zero(qi * qi + I4, "qi^2 = -I")
    assert_matrix_zero(qj * qj + I4, "qj^2 = -I")
    assert_matrix_zero(qk * qk + I4, "qk^2 = -I")
    assert_matrix_zero(qi * qj - qk, "qi*qj = qk")
    assert_matrix_zero(qj * qk - qi, "qj*qk = qi")
    assert_matrix_zero(qk * qi - qj, "qk*qi = qj")
    assert_matrix_zero(qi * qj * qk + I4, "qi*qj*qk = -I")
    print("  gamma-bivector Hamilton table verified")

    q = tuple(sp.symbols("q0 q1 q2 q3", real=True))
    norm_scalar = (qnorm_sq(q), 0, 0, 0)
    for lhs, rhs in zip(qmul(qconj(q), q), norm_scalar):
        assert_zero(lhs - rhs, "conj(Q)Q = normSq(Q)")
    print("  quaternion conjugation/norm identity verified")

    e = {
        (a, mu): sp.symbols(f"e_{a}_{mu}", real=True)
        for a in range(4)
        for mu in range(4)
    }

    def metric(mu, nu):
        return (
            e[(0, mu)] * e[(0, nu)]
            - e[(1, mu)] * e[(1, nu)]
            - e[(2, mu)] * e[(2, nu)]
            - e[(3, mu)] * e[(3, nu)]
        )

    for mu in range(4):
        for nu in range(4):
            assert_zero(metric(mu, nu) - metric(nu, mu), "metric symmetry")
    print("  quaternion-induced metric symmetry verified")

    kappa = sp.symbols("kappa")
    coeff = {
        (lam, mu, nu): sp.symbols(f"B_{lam}_{mu}_{nu}")
        for lam in range(4)
        for mu in range(4)
        for nu in range(4)
    }

    def torsion(lam, mu, nu):
        return kappa * (coeff[(lam, mu, nu)] - coeff[(lam, nu, mu)])

    for lam in range(4):
        for mu in range(4):
            for nu in range(4):
                assert_zero(
                    torsion(lam, nu, mu) + torsion(lam, mu, nu),
                    "torsion lower-index antisymmetry",
                )
    print("  finite torsion commutator antisymmetry verified")

    print("=" * 72)
    print("[SUCCESS] Section 24 theorem-safe finite checks verified.")
    print("=" * 72)


if __name__ == "__main__":
    main()
