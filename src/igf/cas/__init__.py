"""
Computer Algebra System (CAS) and Symbolic Algebra Engine for IGF.
Provides unified, deduplicated implementations of Pauli, Dirac, Clifford, and KMS structures.
"""

from igf.cas.dirac import dirac_gamma_matrices, lorentz_generators
from igf.cas.kms import (
    cantor_tree_partition_sum,
    critical_kms_temperature,
    kms_boltzmann_weight,
    riemann_zeta_kms_factor,
)
from igf.cas.pauli import pauli_anticommutator, pauli_commutator, pauli_matrices

__all__ = [
    "cantor_tree_partition_sum",
    "critical_kms_temperature",
    "dirac_gamma_matrices",
    "kms_boltzmann_weight",
    "lorentz_generators",
    "pauli_anticommutator",
    "pauli_commutator",
    "pauli_matrices",
    "riemann_zeta_kms_factor",
]
