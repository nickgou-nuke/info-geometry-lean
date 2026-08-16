#!/usr/bin/env python3
"""Finite witness for MD 012 emergent-model algebra.

Mirrors `InfoGeometry.Physics.MD012EmergentModelsFinite`.

Verified theorem-safe content only:
* eight-component diagonal covariance and inverse-covariance tables;
* four-component diagonal covariance/sign-stiffness extraction and inverse checks;
* finite density-stress shadow symmetry for symmetric metric data;
* torsion-from-spin and contortion zero-source algebra.

No Gaussian analytic continuation, maximum-entropy existence, Lorentzian
spacetime emergence, action variation, Einstein equation, Dirac equation, ECSK
dynamics, or geometric torsion theorem is claimed.
"""

from __future__ import annotations

import sys
from pathlib import Path
import sympy as sp

_REPO_ROOT = Path(__file__).resolve().parents[2]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

from tools.sympy.common import assert_matrix_zero, assert_zero, mat2


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
    cov4 = sp.diag(1 / (beta * tau), -1 / (beta * kappa), -1 / (beta * kappa), -1 / (beta * kappa))
    assert_zero(metric4[0, 0] - beta * tau, "time-sector metric entry")
    assert_zero(metric4[1, 1] + beta * kappa, "space-sector metric entry")
    assert_matrix_zero(metric4 - metric4.T, "metric4 symmetry")
    assert_matrix_zero(cov4 - cov4.T, "cov4 symmetry")
    assert_matrix_zero(metric4 * cov4 - sp.eye(4), "4x4 sign table times covariance")
    assert_matrix_zero(cov4 * metric4 - sp.eye(4), "4x4 covariance times sign table")
    print("finite covariance/sign-stiffness tables: OK")

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
