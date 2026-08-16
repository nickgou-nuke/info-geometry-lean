"""
Unified Pauli Matrices and SU(2) Spin Algebra for IGF Computer Algebra System.
Canonical deduplicated implementation for all SymPy and CAS physics scripts.
"""

from __future__ import annotations

import sympy as sp
from typing import Tuple


def pauli_matrices() -> Tuple[sp.Matrix, sp.Matrix, sp.Matrix, sp.Matrix]:
    """
    Returns standard 2x2 Pauli matrices (sigma_0, sigma_1, sigma_2, sigma_3):
    sigma_0 = I_2
    sigma_1 = [[0, 1], [1, 0]]
    sigma_2 = [[0, -I], [I, 0]]
    sigma_3 = [[1, 0], [0, -1]]
    """
    I = sp.I
    sigma_0 = sp.Matrix([[1, 0], [0, 1]])
    sigma_1 = sp.Matrix([[0, 1], [1, 0]])
    sigma_2 = sp.Matrix([[0, -I], [I, 0]])
    sigma_3 = sp.Matrix([[1, 0], [0, -1]])
    return sigma_0, sigma_1, sigma_2, sigma_3


def comm(a: sp.Matrix, b: sp.Matrix) -> sp.Matrix:
    """Computes the matrix commutator [A, B] = AB - BA."""
    return a * b - b * a


def pauli_commutator(a: sp.Matrix, b: sp.Matrix) -> sp.Matrix:
    """Alias for matrix commutator [A, B] = AB - BA."""
    return comm(a, b)


def pauli_anticommutator(a: sp.Matrix, b: sp.Matrix) -> sp.Matrix:
    """Computes the matrix anticommutator {A, B} = AB + BA."""
    return a * b + b * a


def mat2(prefix: str) -> sp.Matrix:
    """Generates a generic 2x2 matrix with symbolic entries prefix_ij."""
    return sp.Matrix(2, 2, lambda i, j: sp.symbols(f"{prefix}{i}{j}"))
