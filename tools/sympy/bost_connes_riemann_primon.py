#!/usr/bin/env python3
"""Bost-Connes Riemann Primon Gas & Hilbert-Pólya CPT Verification.

Mirrors:
  * `InfoGeometry.Topology.BostConnesRiemannPrimonBridge`

Verifies:
  1. Supersymmetric Primon Gas & Möbius Witten Index:
       mu(p) = -1, mu(p1 * p2) = +1, mu(p^2 k) = 0 (Nilpotent Pauli exclusion)
  2. Dirichlet Euler-Möbius Inversion:
       sum_{d | n} mu(d) = 1 (if n=1) else 0
  3. Hilbert-Pólya CPT reflection & Critical Line:
       1 - s = s*  <===>  Re(s) = 1/2
  4. PT-Symmetric Hamiltonian:
       J H J^{-1} = -H
"""

from __future__ import annotations

import sys
from pathlib import Path
import sympy as sp

_REPO_ROOT = Path(__file__).resolve().parents[2]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

from tools.sympy.common import assert_matrix_eq


def main() -> None:
    print("=" * 72)
    print("BOST-CONNES RIEMANN PRIMON GAS & HILBERT-PÓLYA VERIFICATION")
    print("=" * 72)

    # 1. Möbius Witten Index spectrum
    primes = [2, 3, 5, 7, 11, 13]
    for p in primes:
        assert sp.mobius(p) == -1, f"Expected mu({p}) == -1"
        assert sp.mobius(p**2) == 0, f"Expected mu({p}^2) == 0 (Pauli exclusion)"

    # Squarefree products
    assert sp.mobius(2 * 3) == 1
    assert sp.mobius(2 * 3 * 5) == -1
    assert sp.mobius(2 * 3 * 5 * 7) == 1

    # 2. Euler-Möbius Inversion (zeta * mu = delta_1)
    for n in range(1, 20):
        div_sum = sum(sp.mobius(d) for d in sp.divisors(n))
        if n == 1:
            assert div_sum == 1, "Expected (zeta * mu)(1) == 1"
        else:
            assert div_sum == 0, f"Expected (zeta * mu)({n}) == 0"

    # 3. Critical line fixed point of s -> 1 - s under complex conjugation
    t = sp.Symbol("t", real=True)
    sigma = sp.Symbol("sigma", real=True)
    s = sigma + sp.I * t

    # 1 - s = s* <=> 1 - sigma - I*t = sigma - I*t <=> 1 - sigma = sigma <=> sigma = 1/2
    refl_s = 1 - s
    conj_s = sp.conjugate(s)
    diff = sp.simplify(refl_s - conj_s)
    # diff is 1 - 2*sigma
    critical_sigma = sp.solve(diff, sigma)[0]
    assert critical_sigma == sp.Rational(1, 2), f"Critical line mismatch: {critical_sigma}"

    # 4. Antiunitary PT reflection matrix
    J = sp.Matrix([[0, 1], [1, 0]])  # Cayley swap
    H = sp.Matrix([[1, 0], [0, -1]])  # Dilatation Hamiltonian
    # J H J^{-1} = -H
    assert_matrix_eq(J * H * J, -H, "PT-reflection J H J^{-1} = -H")

    print("  [OK] Primon gas Witten index & Pauli nilpotency verified: mu(p^2) = 0")
    print("  [OK] Euler-Möbius partition inversion verified: (zeta * mu)(n) = delta_{n,1}")
    print("  [OK] Critical line Re(s) = 1/2 uniquely solved as modular reflection fixed locus")
    print("  [OK] PT-Hamiltonian anti-commutation verified: J H J^{-1} = -H")
    print("=" * 72)
    print("BOST-CONNES RIEMANN PRIMON GAS VERIFIED")
    print("=" * 72)


if __name__ == "__main__":
    main()
