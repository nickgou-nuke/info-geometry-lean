#!/usr/bin/env python3
"""Repaired Section 22: finite quaternion-condensate algebra checks.

This mirrors ``lean/InfoGeometry/Section22.lean``.

Closed finite checks:

* quaternion conjugation gives norm squared;
* real-part bilinear Re(conj(Q) e_a dQ_mu) vanishes for zero derivative;
* metric readout from quaternion-bilinear vielbein coefficients is symmetric;
* Clifford bivectors gamma1 gamma2, gamma2 gamma3, gamma3 gamma1 satisfy the
  Hamilton quaternion multiplication table.

Not claimed here:

* quaternion condensate existence or vacuum expectation values;
* differentiable quaternion field theory;
* emergent nondegenerate vierbein or gravitational bootstrap equations;
* gauge-theoretic physical interpretation.
"""

from __future__ import annotations

import sympy as sp


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
    print("REPAIRED SECTION 22: FINITE QUATERNION-CONDENSATE ALGEBRA")
    print("=" * 72)
    print("Scope: quaternion bilinears, metric symmetry, Clifford bivector embedding.")
    print("Open debt: condensates, fields, gauge interpretation, gravity bootstrap.")

    q = tuple(sp.symbols("q0 q1 q2 q3"))
    zero_q = (sp.Integer(0),) * 4
    norm_scalar = (qnorm_sq(q), 0, 0, 0)
    conj_product = qmul(qconj(q), q)
    for lhs, rhs in zip(conj_product, norm_scalar):
        assert_zero(lhs - rhs, "conj(Q)Q = normSq(Q)")
    print("  quaternion conjugation/norm identity verified")

    basis = [
        (1, 0, 0, 0),
        (0, 1, 0, 0),
        (0, 0, 1, 0),
        (0, 0, 0, 1),
    ]
    for e_a in basis:
        bilinear_zero = qmul(qmul(qconj(q), e_a), zero_q)[0]
        assert_zero(bilinear_zero, "zero-derivative quaternion bilinear")
    print("  zero-derivative real-part bilinear verified")

    e = {
        (a, mu): sp.symbols(f"e_{a}_{mu}")
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
            assert_zero(metric(mu, nu) - metric(nu, mu), "quaternion metric symmetry")
    print("  quaternion-induced metric symmetry verified")

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
    _ = gamma0  # Keeps the full Pauli-Dirac basis visible in the script.

    qi = gamma1 * gamma2
    qj = gamma2 * gamma3
    qk = gamma3 * gamma1
    assert_matrix_zero(qi * qi + I4, "(gamma1 gamma2)^2 = -I")
    assert_matrix_zero(qj * qj + I4, "(gamma2 gamma3)^2 = -I")
    assert_matrix_zero(qk * qk + I4, "(gamma3 gamma1)^2 = -I")
    assert_matrix_zero(qi * qj - qk, "Clifford qi*qj=qk")
    assert_matrix_zero(qj * qk - qi, "Clifford qj*qk=qi")
    assert_matrix_zero(qk * qi - qj, "Clifford qk*qi=qj")
    print("  Clifford bivector quaternion embedding verified")

    print("=" * 72)
    print("[SUCCESS] Section 22 theorem-safe finite checks verified.")
    print("=" * 72)


if __name__ == "__main__":
    main()
