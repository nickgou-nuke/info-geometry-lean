#!/usr/bin/env python3
"""Riemann Hypothesis, Hilbert-Pólya & Primon Partition SymPy Verification.

Mirrors:
  * `InfoGeometry.Topology.RiemannHypothesisHilbertPolyaBridge`

Verifies:
  1. Finite Primon & Parafermionic Partition Algebra:
       (1 - u) * sum_{a=0}^{k-1} u^a = 1 - u^k
       (1 - u) * (1 + u) = 1 - u^2 (Fermion k=2)
  2. Berry-Keating / Bender-Brody-Müller Affine Spectral Inversion:
       E(z) = i(2z - 1),  z(E) = (1 - iE)/2
       z(E(z)) = z,  E(z(E)) = E
  3. Spectral Reality & Critical Line:
       Im(E) = 0  <===>  Re(z(E)) = 1/2
"""

from __future__ import annotations

import sys
from pathlib import Path
import sympy as sp

_REPO_ROOT = Path(__file__).resolve().parents[2]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))


def main() -> None:
    print("=" * 72)
    print("RIEMANN HYPOTHESIS, HILBERT-PÓLYA & PRIMON PARTITION VERIFICATION")
    print("=" * 72)

    # 1. Parafermionic & Fermionic Partition factorization
    u = sp.Symbol("u")
    for k in [2, 3, 4, 5]:
        geom_sum = sum(u**a for a in range(k))
        prod_poly = sp.expand((1 - u) * geom_sum)
        assert prod_poly == 1 - u**k, f"Parafermion k={k} identity failed"
    assert sp.expand((1 - u) * (1 + u)) == 1 - u**2
    print("  [OK] Parafermionic & Fermionic Euler factor factorization verified")

    # 2. Affine Spectral Coordinates
    z = sp.Symbol("z")
    E = sp.Symbol("E")

    def eigenval_of_zero(z_val):
        return sp.I * (2 * z_val - 1)

    def zero_of_eigenval(E_val):
        return (1 - sp.I * E_val) / 2

    assert sp.simplify(zero_of_eigenval(eigenval_of_zero(z)) - z) == 0
    assert sp.simplify(eigenval_of_zero(zero_of_eigenval(E)) - E) == 0
    print("  [OK] Berry-Keating / Bender two-sided affine coordinate inverse verified")

    # 3. Spectral Reality & Critical Line
    E_re, E_im = sp.symbols("E_re E_im", real=True)
    E_complex = E_re + sp.I * E_im
    z_from_E = zero_of_eigenval(E_complex)
    z_re = sp.re(z_from_E)
    # z_re is (1 + E_im)/2
    assert sp.simplify(z_re - (1 + E_im) / 2) == 0

    # Critical line condition Re(z) = 1/2 <=> (1 + E_im)/2 = 1/2 <=> E_im = 0
    solved_E_im = sp.solve(z_re - sp.Rational(1, 2), E_im)[0]
    assert solved_E_im == 0
    print("  [OK] Im(E) = 0 <===> Re(z) = 1/2 spectral criticality verified")

    print("=" * 72)
    print("RIEMANN HYPOTHESIS & HILBERT-PÓLYA COMPANION VERIFIED")
    print("=" * 72)


if __name__ == "__main__":
    main()
