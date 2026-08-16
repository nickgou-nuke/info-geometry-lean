#!/usr/bin/env python3
"""Determinant-level classifier for tripotent matrices.

Companion to `InfoGeometry.Canonical.DeterminantTrifactor`.
It verifies:

  T^3 = T  =>  det(T)^3 = det(T)
            =>  det(T) * (det(T) - 1) * (det(T) + 1) = 0.

No external certificate is used; the factorization is derived by SymPy and the
matrix examples are exact rational/integer computations.
"""

import sys
from pathlib import Path
import sympy as sp

_REPO_ROOT = Path(__file__).resolve().parents[2]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

from tools.sympy.common import assert_matrix_eq


d = sp.Symbol("d")
TRIFACTOR_POLY = d**3 - d


def verify_scalar_factorization() -> None:
    print("Scalar determinant polynomial")
    factored = sp.factor(TRIFACTOR_POLY)
    if factored != d * (d - 1) * (d + 1):
        raise AssertionError(f"unexpected factorization: {factored}")
    print(f"  factor(d^3 - d) = {factored}: OK")

    roots = sorted(sp.solve(sp.Eq(TRIFACTOR_POLY, 0), d), key=str)
    if set(roots) != {-1, 0, 1}:
        raise AssertionError(f"unexpected roots: {roots}")
    print(f"  roots = {roots}: OK")


def verify_matrix(name: str, T: sp.Matrix, expected_det: int) -> None:
    print(f"\nMatrix example: {name}")
    assert_matrix_eq("T^3 = T", T**3, T)

    det_T = sp.simplify(T.det())
    if det_T != expected_det:
        raise AssertionError(f"det(T) expected {expected_det}, got {det_T}")
    print(f"  det(T) = {det_T}: OK")

    det_cube = sp.simplify((T**3).det())
    if det_cube != sp.simplify(det_T**3):
        raise AssertionError(f"det(T^3) != det(T)^3: {det_cube} vs {det_T**3}")
    print("  det(T^3) = det(T)^3: OK")

    if sp.simplify(det_T**3 - det_T) != 0:
        raise AssertionError(f"det(T)^3 != det(T): {det_T}")
    print("  det(T)^3 = det(T): OK")

    if det_T not in {-1, 0, 1}:
        raise AssertionError(f"det(T) not in {{-1,0,1}}: {det_T}")
    print("  det(T) in {-1, 0, 1}: OK")


def main() -> None:
    print("=" * 72)
    print("DETERMINANT TRIFACTOR")
    print("=" * 72)

    verify_scalar_factorization()
    verify_matrix("orientation-preserving diag(+1,+1)", sp.diag(1, 1), 1)
    verify_matrix("orientation-reversing diag(+1,-1)", sp.diag(1, -1), -1)
    verify_matrix("degenerate boundary diag(+1,0,-1)", sp.diag(1, 0, -1), 0)
    verify_matrix("non-diagonal projector", sp.Matrix([[1, 1], [0, 0]]), 0)

    print("\nAll determinant trifactor checks passed.")


if __name__ == "__main__":
    main()
