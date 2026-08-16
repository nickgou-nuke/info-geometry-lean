"""
Unified Cuntz-KMS and Bost-Connes Partition Function Algebra for IGF CAS.
Canonical deduplicated implementation for all thermodynamics, KMS balance, and zeta evaluations.
"""

from __future__ import annotations

import sympy as sp


def critical_kms_temperature() -> sp.Expr:
    """Returns the critical inverse KMS temperature beta_c = ln 2."""
    return sp.log(2)


def kms_boltzmann_weight(n: int = 1) -> sp.Expr:
    """Returns the thermal Boltzmann weight exp(-n * beta_c) = 2^(-n)."""
    return sp.Rational(1, 2**n)


def cantor_tree_partition_sum(depth: int) -> sp.Expr:
    """Computes the finite partition function Z_n = sum_{w in 2^n} 2^(-n) = 1."""
    num_leaves = 2**depth
    leaf_weight = sp.Rational(1, num_leaves)
    return num_leaves * leaf_weight


def riemann_zeta_kms_factor(s: sp.Symbol, prime: int) -> sp.Expr:
    """Returns the local Euler KMS factor (1 - p^(-s))^(-1) for prime p."""
    return 1 / (1 - prime**(-s))
