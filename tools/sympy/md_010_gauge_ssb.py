#!/usr/bin/env python3
"""Finite witness for MD 010 gauge/SSB algebra.

Mirrors `InfoGeometry.Physics.MD010GaugeSSB`.

Verified theorem-safe content only:
* adjoint commutator covariance under finite conjugation with an inverse gate;
* finite product transport `(U F V)(U G V)=U(FG)V` when `VU=I`;
* finite curvature commutator covariance and trace-product invariance;
* scalar potential square completion and stationary radius algebra;
* diagonal E11 vacuum/fluctuation trace identities;
* quaternion U(1)-style unit phase norm invariance;
* zero-connection finite density covariant derivative reduction.

No Yang--Mills field theory, action integral, Standard Model identification,
Higgs mechanism, Goldstone counting, hierarchy generation, Yukawa physics, or
anomaly cancellation theorem is claimed.
"""

from __future__ import annotations

import sys
from pathlib import Path
import sympy as sp

_REPO_ROOT = Path(__file__).resolve().parents[2]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

from tools.sympy.common import assert_matrix_zero, assert_zero, comm, mat2, pauli_matrices


def main() -> int:
    print("=" * 72)
    print("MD 010 FINITE GAUGE / SSB ALGEBRA")
    print("=" * 72)

    # Use a diagonal invertible gauge pair to witness the inverse-gated identities.
    u, v = sp.symbols("u v", nonzero=True)
    U = sp.diag(u, v)
    V = sp.diag(1 / u, 1 / v)
    A = mat2("A")
    Phi = mat2("P")
    F = mat2("F")
    G = mat2("G")

    def conj(X: sp.Matrix) -> sp.Matrix:
        return U * X * V

    assert_matrix_zero(comm(conj(A), conj(Phi)) - conj(comm(A, Phi)), "adjoint commutator covariance")
    assert_matrix_zero(conj(F) * conj(G) - conj(F * G), "finite product transport")

    def curvature(X: sp.Matrix, Y: sp.Matrix) -> sp.Matrix:
        return comm(X, Y)

    assert_matrix_zero(
        curvature(conj(A), conj(Phi)) - conj(curvature(A, Phi)),
        "finite curvature covariance",
    )
    assert_zero(sp.trace(conj(F) * conj(G)) - sp.trace(F * G), "trace-product gauge invariance")
    assert_zero(
        sp.trace(curvature(conj(A), conj(Phi)) * curvature(conj(A), conj(Phi)))
        - sp.trace(curvature(A, Phi) * curvature(A, Phi)),
        "curvature-square trace invariance",
    )
    print("finite gauge covariance/trace invariance identities: OK")

    mu, lam, s = sp.symbols("mu lam s", nonzero=True)
    potential = -mu**2 * s + lam * s**2
    completed = lam * (s - mu**2 / (2 * lam))**2 - mu**4 / (4 * lam)
    assert_zero(potential - completed, "scalar potential square completion")
    stationary = -mu**2 + 2 * lam * (mu**2 / (2 * lam))
    assert_zero(stationary, "stationary radius algebra")
    print("scalar potential algebra: OK")

    E11 = sp.Matrix([[1, 0], [0, 0]])
    vv, h = sp.symbols("vv h")
    vev = vv * E11
    fluct = (vv + h) * E11
    assert_zero(sp.trace(vev * vev) - vv**2, "E11 VEV trace square")
    assert_zero(sp.trace(fluct * fluct) - (vv + h) ** 2, "E11 fluctuation trace square")
    assert_zero(2 * lam * vv**2 - 2 * (lam * vv**2), "quadratic coefficient identity")
    print("diagonal E11 VEV/fluctuation identities: OK")

    c, ss, a, b, cc, d = sp.symbols("c ss a b cc d")
    qnorm = a**2 + b**2 + cc**2 + d**2
    # Left multiplication by phase c + ss*i in quaternion coordinates.
    rotated = [c * a - ss * b, c * b + ss * a, c * cc - ss * d, c * d + ss * cc]
    rotated_norm = sum(x**2 for x in rotated)
    # Exact factorization: rotated_norm - qnorm = (c^2+ss^2-1) qnorm,
    # hence the difference vanishes under the unit-circle premise.
    assert_zero(sp.expand(rotated_norm - (c**2 + ss**2) * qnorm), "quaternion phase norm factorization")
    assert_zero(sp.expand((rotated_norm - qnorm) - (c**2 + ss**2 - 1) * qnorm), "quaternion phase norm unit implication")

    dRho = mat2("D")
    rho = mat2("R")
    zero = sp.zeros(2)
    cov_deriv_zero_conn = dRho + zero * rho - rho * zero
    assert_matrix_zero(cov_deriv_zero_conn - dRho, "zero-connection covariant derivative")
    print("imported finite phase/covariant-derivative stepping stones: OK")

    print("=" * 72)
    print("MD 010 FINITE GAUGE / SSB ALGEBRA VERIFIED")
    print("=" * 72)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
