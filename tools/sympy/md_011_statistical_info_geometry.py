#!/usr/bin/env python3
"""Finite witness for MD 011 statistical/information geometry.

Mirrors `InfoGeometry.Physics.MD011StatisticalInfoGeometry`.

Verified theorem-safe content only:
* finite weighted means/covariances and covariance symmetry;
* constant observable has zero covariance when weights sum to one;
* two-coordinate diagonal quadratic Hamiltonian expansion;
* diagonal inverse-covariance/Fisher matrix is inverse to diagonal covariance
  under reciprocal gates.

No Gaussian integral, continuous Fisher metric, Wasserstein geometry,
entropy-arrow dynamics, Lorentzian-signature emergence, or Einstein-equation
theorem is claimed.
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


def main() -> int:
    print("=" * 72)
    print("MD 011 FINITE STATISTICAL / INFORMATION GEOMETRY")
    print("=" * 72)

    w0, w1 = sp.symbols("w0 w1")
    weights = [w0, w1, 1 - w0 - w1]
    O = sp.symbols("O0 O1 O2")
    P = sp.symbols("P0 P1 P2")

    mean_O = sum(weights[i] * O[i] for i in range(3))
    mean_P = sum(weights[i] * P[i] for i in range(3))
    cov_OP = sum(weights[i] * (O[i] - mean_O) * (P[i] - mean_P) for i in range(3))
    cov_PO = sum(weights[i] * (P[i] - mean_P) * (O[i] - mean_O) for i in range(3))
    assert_zero(cov_OP - cov_PO, "finite covariance symmetry")

    c = sp.symbols("c")
    mean_c = sum(weights[i] * c for i in range(3))
    cov_cP = sum(weights[i] * (c - mean_c) * (P[i] - mean_P) for i in range(3))
    assert_zero(cov_cP, "constant observable zero covariance")
    print("finite covariance identities: OK")

    k0, k1, m0, m1, z0, z1 = sp.symbols("k0 k1 m0 m1 z0 z1")
    energy = sp.Rational(1, 2) * (k0 * (z0 - m0) ** 2 + k1 * (z1 - m1) ** 2)
    expanded = sp.Rational(1, 2) * sum(
        [k0 * (z0 - m0) * (z0 - m0), k1 * (z1 - m1) * (z1 - m1)]
    )
    assert_zero(expanded - energy, "diagonal Gaussian energy expansion")
    print("diagonal quadratic Hamiltonian: OK")

    s0, s1 = sp.symbols("s0 s1", nonzero=True)
    K = sp.diag(1 / s0, 1 / s1)
    S = sp.diag(s0, s1)
    assert_matrix_zero(K * S - sp.eye(2), "inverse covariance times covariance")
    assert_matrix_zero(S * K - sp.eye(2), "covariance times inverse covariance")
    print("diagonal inverse-covariance/Fisher readout: OK")

    print("=" * 72)
    print("MD 011 FINITE STATISTICAL / INFORMATION GEOMETRY VERIFIED")
    print("=" * 72)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
