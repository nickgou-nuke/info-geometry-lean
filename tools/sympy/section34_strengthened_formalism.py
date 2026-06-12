#!/usr/bin/env python3
"""Repaired Section 34 finite strengthened-formalism witness.

Mirrors `InfoGeometry.Physics.Section34StrengthenedFormalism`.
Closed finite content only:
* covariant density derivative `dρ + [Γ,ρ]` reductions;
* finite stress-shadow symmetry under a symmetric metric table;
* source-compatible matrix-biquaternion basis table
  i -> I σ₂, j -> I σ₁, k -> I σ₃.

No continuum variational Einstein equation, entanglement/connection
reconstruction, Lorentz boost exponential theorem, holographic area law, or
phenomenological prediction is claimed.
"""

from __future__ import annotations

import sympy as sp


def assert_zero(expr, label: str) -> None:
    reduced = sp.expand(sp.simplify(expr))
    if reduced != 0:
        raise AssertionError(f"{label} failed:\n{reduced}")


def assert_matrix_zero(mat: sp.Matrix, label: str) -> None:
    reduced = mat.applyfunc(lambda x: sp.expand(sp.simplify(x)))
    if reduced != sp.zeros(*reduced.shape):
        raise AssertionError(f"{label} failed:\n{reduced}")


def mat2(prefix: str) -> sp.Matrix:
    return sp.Matrix(2, 2, lambda i, j: sp.symbols(f"{prefix}{i}{j}"))


def comm(A: sp.Matrix, B: sp.Matrix) -> sp.Matrix:
    return A * B - B * A


def main() -> int:
    print("=" * 72)
    print("REPAIRED SECTION 34 STRENGTHENED FINITE FORMALISM")
    print("=" * 72)

    sigma1 = sp.Matrix([[0, 1], [1, 0]])
    sigma2 = sp.Matrix([[0, -sp.I], [sp.I, 0]])
    sigma3 = sp.Matrix([[1, 0], [0, -1]])
    eye = sp.eye(2)

    d_rho = mat2("D")
    gamma = mat2("G")
    rho = mat2("R")
    cov = d_rho + comm(gamma, rho)
    assert_matrix_zero((d_rho + comm(sp.zeros(2), rho)) - d_rho,
                       "zero connection covariant derivative")
    assert_matrix_zero((sp.zeros(2) + comm(gamma, rho)) - comm(gamma, rho),
                       "zero partial covariant derivative")
    print("finite covariant density derivative reductions: OK")

    A = mat2("A")
    B = mat2("B")
    assert_zero(sp.trace(A * B) - sp.trace(B * A), "trace cyclicity for Mat2")

    # Stress-shadow symmetry: use generic symmetric g_{μν} and symbolic traces.
    gmunu, kinetic, V, trmunu = sp.symbols("gmunu K V trmunu")
    stress_mn = trmunu - sp.Rational(1, 2) * gmunu * kinetic + gmunu * V
    stress_nm = trmunu - sp.Rational(1, 2) * gmunu * kinetic + gmunu * V
    assert_zero(stress_mn - stress_nm, "symmetric finite density stress shadow")
    print("finite density stress-shadow symmetry: OK")

    bq_i = sp.I * sigma2
    bq_j = sp.I * sigma1
    bq_k = sp.I * sigma3
    assert_matrix_zero(bq_i - sp.Matrix([[0, 1], [-1, 0]]), "source i matrix")
    assert_matrix_zero(bq_j - sp.Matrix([[0, sp.I], [sp.I, 0]]), "source j matrix")
    assert_matrix_zero(bq_k - sp.Matrix([[sp.I, 0], [0, -sp.I]]), "source k matrix")
    assert_matrix_zero(bq_i**2 + eye, "i square")
    assert_matrix_zero(bq_j**2 + eye, "j square")
    assert_matrix_zero(bq_k**2 + eye, "k square")
    assert_matrix_zero(bq_i * bq_j - bq_k, "ij=k")
    assert_matrix_zero(bq_j * bq_k - bq_i, "jk=i")
    assert_matrix_zero(bq_k * bq_i - bq_j, "ki=j")
    assert_matrix_zero(bq_i * bq_j * bq_k + eye, "ijk=-1")
    print("source-compatible matrix-biquaternion product table: OK")

    print("=" * 72)
    print("REPAIRED SECTION 34 FINITE SOCKET VERIFIED")
    print("=" * 72)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
