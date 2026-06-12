#!/usr/bin/env python3
"""Repaired Section 33 finite Pauli/biquaternion completion witness.

Mirrors `InfoGeometry.Physics.Section33PauliBiquaternionCompletion`.
Closed finite content only:
* every 2x2 complex matrix decomposes in the Pauli basis;
* radius-r Bloch density is idempotent under r^2(n1^2+n2^2+n3^2)=1;
* the same boundary gives determinant-zero density/spacetime certificates;
* finite biquaternion pairs are just two Pauli-matrix components with an
  involutive dual swap.

No Dirac-equation equivalence, Einstein equation, torsion emergence,
entanglement/connection theorem, holographic area law, black-hole correction,
gravity-wave equation, or phenomenological prediction is claimed.
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
    print("REPAIRED SECTION 33 PAULI/BIQUATERNION COMPLETION")
    print("=" * 72)

    sigma0 = sp.eye(2)
    sigma1 = sp.Matrix([[0, 1], [1, 0]])
    sigma2 = sp.Matrix([[0, -sp.I], [sp.I, 0]])
    sigma3 = sp.Matrix([[1, 0], [0, -1]])

    A = mat2("A")
    c0 = (A[0, 0] + A[1, 1]) / 2
    c1 = (A[0, 1] + A[1, 0]) / 2
    c2 = sp.I / 2 * (A[0, 1] - A[1, 0])
    c3 = (A[0, 0] - A[1, 1]) / 2
    recomposed = c0*sigma0 + c1*sigma1 + c2*sigma2 + c3*sigma3
    assert_matrix_zero(recomposed - A, "Pauli recomposition of arbitrary Mat2")
    assert_zero(c0 - sp.trace(A) / 2, "scalar coefficient trace readback")
    print("Pauli basis completion for Mat2(C): OK")

    r, n1, n2, n3, t = sp.symbols("r n1 n2 n3 t")
    rho = sp.Matrix([
        [(1 + r*n3) / 2, (r*n1 - sp.I*r*n2) / 2],
        [(r*n1 + sp.I*r*n2) / 2, (1 - r*n3) / 2],
    ])
    unit_expr = r**2 * (n1**2 + n2**2 + n3**2)
    idem_gap = rho*rho - rho
    # The diagonal gaps and determinant are explicit multiples of the
    # scaled-unit residual `r^2(n1^2+n2^2+n3^2)-1`.
    residual = unit_expr - 1
    assert_zero(idem_gap[0, 0] - residual / 4, "density idempotent diagonal 00 residual")
    assert_zero(idem_gap[1, 1] - residual / 4, "density idempotent diagonal 11 residual")
    assert_zero(idem_gap[0, 1], "density idempotent offdiag 01")
    assert_zero(idem_gap[1, 0], "density idempotent offdiag 10")
    assert_zero(rho.det() + residual / 4, "density determinant residual")
    print("scaled-unit Bloch purity certificates: OK")

    point = sp.Matrix([
        [t + t*r*n3, t*r*n1 - sp.I*t*r*n2],
        [t*r*n1 + sp.I*t*r*n2, t - t*r*n3],
    ])
    assert_zero(point.det() + t**2 * residual, "spacetime point determinant residual")
    print("scaled-unit null boundary certificate: OK")

    # Finite biquaternion-pair dual swap: (P,D) -> (D,P) -> (P,D).
    primal = mat2("P")
    dual = mat2("D")
    swapped = (dual, primal)
    swapped_twice = (swapped[1], swapped[0])
    assert_matrix_zero(swapped_twice[0] - primal, "dual swap primal involution")
    assert_matrix_zero(swapped_twice[1] - dual, "dual swap dual involution")
    print("finite biquaternion-pair dual swap: OK")

    print("=" * 72)
    print("REPAIRED SECTION 33 FINITE SOCKET VERIFIED")
    print("=" * 72)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
