#!/usr/bin/env python3
"""
Shared Mathematical & Verification Utilities for SymPy Symbolic Verification Scripts.

Compatibility wrapper forwarding to the unified `igf.cas` package.
"""

from __future__ import annotations

import sys
from pathlib import Path

# Repository Root Resolution
_REPO_ROOT = Path(__file__).resolve().parents[2]
_SRC = _REPO_ROOT / "src"
if str(_SRC) not in sys.path:
    sys.path.insert(0, str(_SRC))
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

from igf.cas.assertions import (
    assert_matrix_eq,
    assert_matrix_equal,
    assert_matrix_zero,
    assert_zero,
    symmetric_2x2,
)
from igf.cas.pauli import comm, mat2, pauli_anticommutator, pauli_commutator, pauli_matrices

__all__ = [
    "assert_matrix_eq",
    "assert_matrix_equal",
    "assert_matrix_zero",
    "assert_zero",
    "comm",
    "mat2",
    "pauli_anticommutator",
    "pauli_commutator",
    "pauli_matrices",
    "symmetric_2x2",
]
