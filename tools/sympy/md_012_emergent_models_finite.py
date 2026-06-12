#!/usr/bin/env python3
"""Finite witness for MD 012 emergent-model algebra.

Mirrors `InfoGeometry.Physics.MD012EmergentModelsFinite`.

Verified theorem-safe content only:
* eight-component diagonal covariance and inverse-covariance tables;
* four-component diagonal sign/stiffness extraction;
* finite density-stress shadow symmetry for symmetric metric data;
* torsion-from-spin and contortion zero-source algebra.

No Gaussian analytic continuation, maximum-entropy existence, Lorentzian
spacetime emergence, action variation, Einstein equation, Dirac equation, ECSK
dynamics, or geometric torsion theorem is claimed.
"""

from __future__ import annotations

import sympy as sp


def assert_zero(expr, label: str) -> None:
    reduced = sp.expand(sp.simplify(expr))
    if reduced != 0:
        raise AssertionError(f"{label} failed: {reduced}")


def assert_matrix_zero(mat: sp.Matrix, label: str) -> None:
    reduced = mat.applyfunc(lambda x: sp.expand(sp.simplify(x)))
    if reduced != sp.zeros(*reduced.shape):
        raise AssertionError(f"{label} failed:\n{reduced}")


def mat2(prefix: str) -> sp.Matrix:
    return sp.Matrix(2, 2, lambda i, j: sp.symbols(f"{prefix}{i}{j}"))


def main() -> int:
    print("=" * 72)
    print("MD 012 FINITE EMERGENT-MODEL SHADOWS")
    print("=" * 72)

    beta, tau, kappa = sp.symbols("beta tau kappa", nonzero=True)
    cov_diag = [1 / (beta * tau), 1 / (beta * tau)] + [-1 / (beta * kappa)] * 6
    inv_diag = [beta * tau, beta * tau] + [-beta * kappa] * 6
    Sigma = sp.diag(*cov_diag)
    Sigma_inv = sp.diag(*inv_diag)
    assert_matrix_zero(Sigma_inv * Sigma - sp.eye(8), "8x8 inverse covariance left inverse")
    assert_matrix_zero(Sigma * Sigma_inv - sp.eye(8), "8x8 inverse covariance right inverse")
    print("diagonal covariance/inverse covariance: OK")

    metric4 = sp.diag(beta * tau, -beta * kappa, -beta * kappa, -beta * kappa)
    assert_zero(metric4[0, 0] - beta * tau, "time-sector metric entry")
    assert_zero(metric4[1, 1] + beta * kappa, "space-sector metric entry")
    assert_matrix_zero(metric4 - metric4.T, "metric4 symmetry")
    print("finite sign/stiffness table: OK")

    # Symmetric finite density-stress shadow sample over four indices.
    g = sp.Matrix(4, 4, lambda i, j: sp.symbols(f"g{min(i,j)}{max(i,j)}"))
    V = sp.symbols("V")
    rhoD = [mat2(f"R{a}") for a in range(4)]

    def tr(A: sp.Matrix) -> sp.Expr:
        return sp.trace(A)

    kinetic = sum(g[a, b] * tr(rhoD[a] * rhoD[b]) for a in range(4) for b in range(4))

    def stress(mu: int, nu: int) -> sp.Expr:
        return tr(rhoD[mu] * rhoD[nu]) - sp.Rational(1, 2) * g[mu, nu] * kinetic + g[mu, nu] * V

    assert_zero(stress(1, 3) - stress(3, 1), "finite density-stress symmetry sample")
    print("finite density-stress shadow symmetry: OK")

    kap = sp.symbols("kap")
    zero_spin = [[[sp.Integer(0) for _ in range(4)] for _ in range(4)] for _ in range(4)]
    torsion = [[[kap * zero_spin[a][b][c] for c in range(4)] for b in range(4)] for a in range(4)]
    contortion = [
        [
            [sp.Rational(1, 2) * (torsion[a][b][c] + torsion[b][a][c] + torsion[c][a][b]) for c in range(4)]
            for b in range(4)
        ]
        for a in range(4)
    ]
    for a in range(4):
        for b in range(4):
            for c in range(4):
                assert_zero(torsion[a][b][c], f"zero spin -> zero torsion {a}{b}{c}")
                assert_zero(contortion[a][b][c], f"zero torsion -> zero contortion {a}{b}{c}")
    print("torsion/contortion zero-source algebra: OK")

    print("=" * 72)
    print("MD 012 FINITE EMERGENT-MODEL SHADOWS VERIFIED")
    print("=" * 72)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
