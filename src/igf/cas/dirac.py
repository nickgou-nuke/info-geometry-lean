"""
Unified Dirac Gamma Matrices and Clifford Cl(1,3) Algebra for IGF CAS.
Canonical deduplicated implementation for all relativistic spacetime and twistor scripts.
"""

from __future__ import annotations

import sympy as sp
from typing import Tuple
from igf.cas.pauli import pauli_matrices


def dirac_gamma_matrices(basis: str = "dirac") -> Tuple[sp.Matrix, sp.Matrix, sp.Matrix, sp.Matrix, sp.Matrix]:
    """
    Returns 4x4 Dirac gamma matrices (gamma_0, gamma_1, gamma_2, gamma_3, gamma_5)
    in the standard Dirac-Pauli or Weyl chiral basis.
    Metric signature: diag(+1, -1, -1, -1).
    """
    s0, s1, s2, s3 = pauli_matrices()
    z2 = sp.zeros(2, 2)

    if basis.lower() == "weyl":
        # Chiral / Weyl basis
        g0 = sp.BlockMatrix([[z2, s0], [s0, z2]]).as_explicit()
        g1 = sp.BlockMatrix([[z2, s1], [-s1, z2]]).as_explicit()
        g2 = sp.BlockMatrix([[z2, s2], [-s2, z2]]).as_explicit()
        g3 = sp.BlockMatrix([[z2, s3], [-s3, z2]]).as_explicit()
        g5 = sp.BlockMatrix([[-s0, z2], [z2, s0]]).as_explicit()
    else:
        # Standard Dirac-Pauli basis
        g0 = sp.BlockMatrix([[s0, z2], [z2, -s0]]).as_explicit()
        g1 = sp.BlockMatrix([[z2, s1], [-s1, z2]]).as_explicit()
        g2 = sp.BlockMatrix([[z2, s2], [-s2, z2]]).as_explicit()
        g3 = sp.BlockMatrix([[z2, s3], [-s3, z2]]).as_explicit()
        # gamma^5 = i * gamma^0 * gamma^1 * gamma^2 * gamma^3
        g5 = (sp.I * g0 * g1 * g2 * g3).as_explicit()

    return g0, g1, g2, g3, g5


def lorentz_generators() -> dict[Tuple[int, int], sp.Matrix]:
    """
    Returns the Lorentz group Spin(1,3) generators S_mu_nu = (i/4) * [gamma_mu, gamma_nu].
    """
    g0, g1, g2, g3, _ = dirac_gamma_matrices("dirac")
    gammas = [g0, g1, g2, g3]
    gens = {}
    for mu in range(4):
        for nu in range(4):
            if mu < nu:
                comm = gammas[mu] * gammas[nu] - gammas[nu] * gammas[mu]
                gens[(mu, nu)] = (sp.I / 4) * comm
    return gens
