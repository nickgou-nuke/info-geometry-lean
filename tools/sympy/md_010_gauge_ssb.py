#!/usr/bin/env python3
"""Finite witness for MD 010 gauge/SSB algebra.

Mirrors `InfoGeometry.Physics.MD010GaugeSSB`.

Verified theorem-safe content only:
* adjoint commutator covariance under finite conjugation with an inverse gate;
* finite product transport `(U F V)(U G V)=U(FG)V` when `VU=I`;
* scalar potential square completion and stationary radius algebra;
* diagonal E11 vacuum/fluctuation trace identities;
* quaternion U(1)-style unit phase norm invariance;
* zero-connection finite density covariant derivative reduction.

No Yang--Mills field theory, action integral, Standard Model identification,
Higgs mechanism, Goldstone counting, hierarchy generation, Yukawa physics, or
anomaly cancellation theorem is claimed.
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

    def comm(X: sp.Matrix, Y: sp.Matrix) -> sp.Matrix:
        return X * Y - Y * X

    assert_matrix_zero(comm(conj(A), conj(Phi)) - conj(comm(A, Phi)), "adjoint commutator covariance")
    assert_matrix_zero(conj(F) * conj(G) - conj(F * G), "finite product transport")
    print("finite gauge covariance identities: OK")

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
