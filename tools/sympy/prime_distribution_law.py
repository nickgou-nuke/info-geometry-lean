#!/usr/bin/env python3
"""Empirical prime-distribution verifier.

This script computes finite prime-distribution observables:

* prime count pi(N)
* local density pi(N) / N versus 1 / log(N)
* Chebyshev theta(N) = sum_{p <= N} log p
* Chebyshev psi(N) = sum_{p^k <= N} log p
* average prime gap
* residue-class counts modulo q

It verifies exact finite bookkeeping identities.  It does not prove the Prime
Number Theorem, RH, or Hardy--Littlewood; those are asymptotic laws, not finite
symbolic identities.
"""

from __future__ import annotations

import math
from collections import Counter

import sympy as sp


def primes_up_to(n: int) -> list[int]:
    return list(sp.primerange(1, n + 1))


def prime_count(n: int) -> int:
    return len(primes_up_to(n))


def chebyshev_theta(n: int) -> float:
    return sum(math.log(p) for p in primes_up_to(n))


def chebyshev_psi(n: int) -> float:
    total = 0.0
    for p in primes_up_to(n):
        power = p
        while power <= n:
            total += math.log(p)
            power *= p
    return total


def prime_gaps(primes: list[int]) -> list[int]:
    return [b - a for a, b in zip(primes, primes[1:], strict=False)]


def residue_counts(primes: list[int], q: int) -> Counter[int]:
    return Counter(p % q for p in primes)


def main() -> None:
    cutoffs = [100, 1_000, 10_000, 100_000]
    q = 10
    rows: list[tuple[int, int, float, float, float, float, float]] = []

    for n in cutoffs:
        primes = primes_up_to(n)
        pi_n = len(primes)
        density = pi_n / n
        local_model = 1 / math.log(n)
        theta = chebyshev_theta(n)
        psi = chebyshev_psi(n)
        gaps = prime_gaps(primes)
        avg_gap = sum(gaps) / len(gaps)

        assert pi_n == prime_count(n)
        assert len(gaps) == max(pi_n - 1, 0)
        assert math.isclose(avg_gap, (primes[-1] - primes[0]) / (pi_n - 1))
        assert theta <= psi + 1e-9

        residues = residue_counts(primes, q)
        assert sum(residues.values()) == pi_n
        allowed_residue_count = sum(residues[r] for r in [1, 3, 7, 9])
        special_count = residues[2] + residues[5]
        assert allowed_residue_count + special_count == pi_n

        rows.append((n, pi_n, density, local_model, theta / n, psi / n, avg_gap))

    print("prime_distribution_law: ok")
    print("  N      pi(N)   pi(N)/N    1/log(N)   theta(N)/N   psi(N)/N   avg_gap")
    for n, pi_n, density, local_model, theta_ratio, psi_ratio, avg_gap in rows:
        print(
            f"  {n:<6} {pi_n:<7} {density:0.6f}  {local_model:0.6f}  "
            f"{theta_ratio:0.6f}    {psi_ratio:0.6f}   {avg_gap:0.3f}"
        )

    residues = residue_counts(primes_up_to(cutoffs[-1]), q)
    print(f"  residue_counts_mod_{q}: {dict(sorted(residues.items()))}")
    print("  exact_finite_checks: count, gaps, theta<=psi, residue partition")


if __name__ == "__main__":
    main()
