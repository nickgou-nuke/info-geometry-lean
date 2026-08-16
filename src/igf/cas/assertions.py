"""
Unified Symbolic Assertions and Matrix Equivalence Checkers for IGF CAS.
Canonical deduplicated implementation for all mathematical test suites and sympy verifications.
"""

from __future__ import annotations

from typing import Any
import sympy as sp


def assert_zero(expr: Any, label: str = "Expression") -> None:
    """Asserts that a symbolic expression simplifies identically to zero."""
    reduced = sp.expand(sp.simplify(expr))
    if reduced != 0:
        raise AssertionError(f"{label} failed to vanish: {reduced}")


def assert_matrix_zero(mat: Any, label: str = "Matrix") -> None:
    """Asserts that all entries of a matrix simplify identically to zero."""
    if hasattr(mat, "shape") and not hasattr(mat, "applyfunc"):
        import numpy as np
        if not np.all(mat == 0):
            raise AssertionError(f"{label} failed to vanish identically:\n{mat}")
        return
    reduced = mat.applyfunc(lambda x: sp.expand(sp.simplify(x)))
    if reduced != sp.zeros(*reduced.shape):
        raise AssertionError(f"{label} failed to vanish identically:\n{reduced}")


def assert_matrix_equal(
    mat1: Any,
    mat2: Any = None,
    label: Any = "Matrix equality",
) -> None:
    """Asserts that two matrices are symbolically equal.

    Supports both standard (mat1, mat2, label="...") and reversed (label, actual, expected) signatures.
    """
    if isinstance(mat1, str):
        label_text = mat1
        actual = mat2
        expected = label
        diff = actual - expected
        assert_matrix_zero(diff, label_text)
    else:
        diff = mat1 - mat2
        assert_matrix_zero(diff, str(label))


assert_matrix_eq = assert_matrix_equal


def symmetric_2x2(prefix: str) -> sp.Matrix:
    """Generates a generic 2x2 complex symmetric matrix."""
    a, b, c = sp.symbols(f"{prefix}00 {prefix}01 {prefix}11", complex=True)
    return sp.Matrix([[a, b], [b, c]])
