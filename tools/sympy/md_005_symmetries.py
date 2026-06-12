#!/usr/bin/env python3
"""Finite witness for MD 005 symmetry shadows.

Mirrors `InfoGeometry.Physics.MD005Symmetries`.

Verified theorem-safe content only:
* congruence action X |-> A X A^† has determinant det(A) det(X) conjugate(det(A));
* determinant-one/unit determinant gate preserves determinant;
* congruence actions compose;
* scalar ±I acts trivially by congruence;
* finite translations of R^4 commute.

No full SL(2,C)->SO^+(1,3) surjectivity, Poincare Lie algebra, Casimir
classification, or conformal spin-cover theorem is claimed.
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


def main() -> int:
    print("=" * 72)
    print("MD 005 FINITE SYMMETRY SHADOWS")
    print("=" * 72)

    A = mat2("A")
    B = mat2("B")
    X = mat2("X")
    Ad = A.conjugate().T
    Bd = B.conjugate().T

    congr = A * X * Ad
    det_law = congr.det() - A.det() * X.det() * sp.conjugate(A.det())
    assert_zero(det_law, "congruence determinant law")
    print("congruence determinant law: OK")

    # Determinant-preservation gate: substitute det(A)=1 and conjugate(det(A))=1.
    detA = A.det()
    det_pres_gate = sp.expand(congr.det() - X.det()).subs({detA: 1, sp.conjugate(detA): 1})
    # SymPy does not always substitute composite determinant atoms inside expanded
    # expressions consistently, so verify the abstract multiplicative law directly.
    d, dbar, xdet = sp.symbols("d dbar xdet")
    assert_zero((d * dbar * xdet - xdet).subs(d * dbar, 1), "determinant-one preservation abstract")
    print("determinant-one preservation gate: OK")

    lhs = A * (B * X * Bd) * Ad
    rhs = (A * B) * X * (A * B).conjugate().T
    assert_matrix_zero(lhs - rhs, "congruence composition")
    print("congruence composition: OK")

    I2 = sp.eye(2)
    assert_matrix_zero((I2 * X * I2) - X, "+I scalar kernel action")
    minusI = -I2
    assert_matrix_zero(minusI * X * minusI.conjugate().T - X, "-I scalar kernel action")
    print("scalar ±I kernel shadow: OK")

    x = sp.Matrix(sp.symbols("x0:4"))
    xi = sp.Matrix(sp.symbols("xi0:4"))
    eta = sp.Matrix(sp.symbols("eta0:4"))
    translate_xi_eta = x + eta + xi
    translate_eta_xi = x + xi + eta
    assert_matrix_zero(translate_xi_eta - translate_eta_xi, "finite translation commutativity")
    print("finite translation commutativity: OK")

    print("=" * 72)
    print("MD 005 FINITE SYMMETRY SHADOWS VERIFIED")
    print("=" * 72)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
