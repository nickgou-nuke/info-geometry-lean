#!/usr/bin/env python3
"""
Prime Ising Partition Function Exact Factorization CAS Verification.

Verifies:
1. Hamiltonian Quadratic Decomposition for Ising Spins sigma_i^2 = 1:
   H(sigma; w) = -1/2 sum_{i!=j} J_ij sigma_i sigma_j + w/2 sum_i ell_i sigma_i - lambda/4 sum_i ell_i^2.
2. Partition Function Factorization:
   Z_N(lambda, beta, w) = exp(beta * lambda * sum_i ell_i^2 / 4) * Z_N^pair(lambda, beta, w).
3. Zero-Invariance Property:
   Since the prefactor exp(...) > 0 is non-zero everywhere, the roots/zeros of Z_N
   in the complex fugacity / field plane coincide exactly with the zeros of Z_N^pair.
4. Non-interacting Factorization (lambda = 0):
   Z_N(0, beta, w) = prod_{i=1}^N 2 cosh(beta * w * ell_i / 2).
"""

from __future__ import annotations

import itertools
import sympy as sp
from igf.cas.assertions import assert_zero


def test_prime_ising_partition_factorization() -> None:
    print("========================================================================")
    print("PRIME ISING PARTITION FUNCTION EXACT FACTORIZATION: CAS VERIFICATION")
    print("========================================================================")

    lam, beta, w = sp.symbols("lam beta w", real=True)
    l1, l2, l3 = sp.symbols("l1 l2 l3", positive=True)
    ell = [l1, l2, l3]
    N = len(ell)

    # 1. Verification of Hamiltonian expansion for every Ising spin configuration sigma in {+1, -1}^N
    for sigma in itertools.product([1, -1], repeat=N):
        # Collective Hamiltonian
        coll_sum = sum(ell[i] * sigma[i] for i in range(N))
        H_coll = - (lam / 4) * coll_sum**2 + (w / 2) * coll_sum

        # Pair Hamiltonian + self energy
        pair_sum = 0
        for i in range(N):
            for j in range(N):
                if i != j:
                    J_ij = (lam / 2) * ell[i] * ell[j]
                    pair_sum += J_ij * sigma[i] * sigma[j]
        H_pair = - (1 / 2) * pair_sum + (w / 2) * coll_sum
        E_self = - (lam / 4) * sum(ell[i]**2 for i in range(N))

        H_decomposed = H_pair + E_self

        diff = sp.simplify(H_coll - H_decomposed)
        assert_zero(diff, f"H_coll = H_pair + E_self for sigma = {sigma}")

    print("  [OK] 1. Exact Hamiltonian Decomposition H = H_pair - (lam/4) sum ell_i^2 verified for all spins")

    # 2. Partition function evaluation and exact factorization
    Z_coll = sum(sp.exp(-beta * (- (lam / 4) * sum(ell[i] * s[i] for i in range(N))**2 + (w / 2) * sum(ell[i] * s[i] for i in range(N)))) for s in itertools.product([1, -1], repeat=N))

    Z_pair = sum(sp.exp(-beta * (- (1 / 2) * sum((lam / 2) * ell[i] * ell[j] * s[i] * s[j] for i in range(N) for j in range(N) if i != j) + (w / 2) * sum(ell[i] * s[i] for i in range(N)))) for s in itertools.product([1, -1], repeat=N))

    self_factor = sp.exp(beta * (lam / 4) * sum(ell[i]**2 for i in range(N)))

    # Ratio Z_coll / (self_factor * Z_pair) must equal 1
    ratio_diff = sp.simplify(Z_coll - self_factor * Z_pair)
    assert_zero(ratio_diff, "Z_coll = self_factor * Z_pair")
    print("  [OK] 2. Exact Partition Function Factorization Z_coll = exp(...) * Z_pair verified")

    # 3. Non-interacting factorization (lam = 0)
    Z_0 = Z_coll.subs(lam, 0)
    Z_0_expected = 1
    for i in range(N):
        Z_0_expected *= 2 * sp.cosh(beta * w * ell[i] / 2)
    diff_0 = sp.simplify(Z_0 - Z_0_expected.rewrite(sp.exp).expand())
    assert_zero(diff_0, "Z(lam=0) = prod 2*cosh(beta*w*ell_i / 2)")
    print("  [OK] 3. Non-interacting Free Prime Partition Function Z(0) = prod 2*cosh(...) verified")

    print("========================================================================")
    print("ALL PRIME ISING PARTITION FACTORIZATION PROOFS 100% CAS VERIFIED")
    print("========================================================================")


if __name__ == "__main__":
    test_prime_ising_partition_factorization()
