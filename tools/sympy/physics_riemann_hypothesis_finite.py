#!/usr/bin/env python3
"""
Assertion-backed finite verifier for arXiv:1101.3116v1,
"Physics of the Riemann Hypothesis" (Schumayer--Hutchinson).

This is deliberately theorem-safe finite mathematics only.  It checks exact
arithmetic shadows that the review uses as inputs:

* finite Euler-factor / prime-product algebra at k = 2,
* Mobius divisor sums and the square-divisibility zero mode,
* prime-counting by direct sieve versus SymPy's primepi,
* Mertens summatory values as finite data.

It does NOT verify RH, Hilbert--Polya, quantum-chaos spectral claims,
Riemann-von Mangoldt asymptotics, analytic continuation, or any physical
operator model.
"""

from __future__ import annotations

from fractions import Fraction
from math import prod

import sympy as sp


def mobius_by_definition(n: int) -> int:
    """Mobius function from the squarefree prime-factor definition."""
    if n == 1:
        return 1
    fac = sp.factorint(n)
    if any(exp > 1 for exp in fac.values()):
        return 0
    return -1 if len(fac) % 2 else 1


def divisors(n: int) -> list[int]:
    return sorted(int(d) for d in sp.divisors(n))


def truncated_euler_factor(primes: list[int], k: int, exponent_bound: int) -> Fraction:
    """prod_p sum_{a=0}^{B} p^{-ka}, exactly as a rational."""
    total = Fraction(1, 1)
    for p in primes:
        total *= sum(Fraction(1, p ** (k * a)) for a in range(exponent_bound + 1))
    return total


def smooth_dirichlet_sum(primes: list[int], k: int, exponent_bound: int) -> Fraction:
    """sum over all products prod p^a, 0 <= a <= B, of n^{-k}."""
    terms = [Fraction(1, 1)]
    for p in primes:
        terms = [term * Fraction(1, p ** (k * a)) for term in terms for a in range(exponent_bound + 1)]
    return sum(terms, Fraction(0, 1))


def prime_count_by_sieve(limit: int) -> int:
    if limit < 2:
        return 0
    is_prime = [True] * (limit + 1)
    is_prime[0] = is_prime[1] = False
    for p in range(2, int(limit**0.5) + 1):
        if is_prime[p]:
            for q in range(p * p, limit + 1, p):
                is_prime[q] = False
    return sum(is_prime)


def main() -> None:
    # Euler product finite algebra: exact distributivity for the first two
    # primes, k=2, exponent bound 3.  This is the finite shadow of equation (2),
    # not the infinite analytic theorem.
    primes = [2, 3]
    k = 2
    exponent_bound = 3
    factor_side = truncated_euler_factor(primes, k, exponent_bound)
    sum_side = smooth_dirichlet_sum(primes, k, exponent_bound)
    assert factor_side == sum_side
    assert factor_side == Fraction(17425, 11664)

    # Nonzero Euler factors in the original half-plane example k=2.
    for p in [2, 3, 5, 7, 11, 13]:
        factor = Fraction(1, 1) - Fraction(1, p**2)
        assert factor != 0
        assert factor > 0

    # Finite primon/Bost-Connes partition shadow at beta=2 on primes {2,3}:
    # bosonic product times signed-fermion/Mobius product cancels exactly.
    signed_mobius = prod(Fraction(1, 1) - Fraction(1, p**2) for p in primes)
    bosonic = prod(Fraction(1, 1) / (Fraction(1, 1) - Fraction(1, p**2)) for p in primes)
    assert signed_mobius == Fraction(2, 3)
    assert bosonic == Fraction(3, 2)
    assert bosonic * signed_mobius == 1

    # Paper eqs. (58)--(59), in finite Euler-factor form.  For occupation
    # bound kappa, the local factor is (1 - p^(-kappa*s))/(1 - p^(-s)) =
    # 1 + p^(-s) + ... + p^(-(kappa-1)*s).  This proves only the finite
    # {2,3}, s=2 arithmetic identity, not an infinite zeta quotient theorem.
    finite_fermion = prod(sum(Fraction(1, p ** (2 * a)) for a in range(2)) for p in primes)
    finite_parafermion3 = prod(sum(Fraction(1, p ** (2 * a)) for a in range(3)) for p in primes)
    quotient_fermion = prod(
        (Fraction(1, 1) - Fraction(1, p ** 4)) / (Fraction(1, 1) - Fraction(1, p ** 2))
        for p in primes
    )
    quotient_parafermion3 = prod(
        (Fraction(1, 1) - Fraction(1, p ** 6)) / (Fraction(1, 1) - Fraction(1, p ** 2))
        for p in primes
    )
    assert finite_fermion == quotient_fermion == Fraction(25, 18)
    assert finite_parafermion3 == quotient_parafermion3 == Fraction(637, 432)

    # Mobius definition from the paper's footnote and standard divisor sums.
    for n in range(1, 101):
        assert mobius_by_definition(n) == int(sp.mobius(n))
        divisor_sum = sum(mobius_by_definition(d) for d in divisors(n))
        assert divisor_sum == (1 if n == 1 else 0)

    # Square-divisibility zero mode highlighted by mu(n)=0.
    for n in [4, 8, 9, 12, 16, 18, 20, 24, 25, 27, 28, 36]:
        assert mobius_by_definition(n) == 0

    # Direct prime counting finite readout, matching SymPy's implementation.
    expected_pi = {10: 4, 30: 10, 100: 25, 200: 46}
    for limit, expected in expected_pi.items():
        assert prime_count_by_sieve(limit) == expected
        assert int(sp.primepi(limit)) == expected

    # Mertens finite data: useful for locating anomalies, not an RH proof.
    mertens = {n: sum(mobius_by_definition(j) for j in range(1, n + 1)) for n in range(1, 51)}
    assert mertens[1] == 1
    assert mertens[10] == -1
    assert mertens[50] == -3

    print("physics_rh_finite: all exact SymPy assertions passed")
    print("finite_euler_2_3_k2_B3 =", factor_side)
    print("finite_primon_boson_x_signed_mobius =", bosonic * signed_mobius)
    print("finite_fermion_primon_Z2_over_2_3_s2 =", finite_fermion)
    print("finite_parafermion_kappa3_over_2_3_s2 =", finite_parafermion3)
    print("scope: finite arithmetic only; no RH / Hilbert-Polya / analytic-continuation proof")


if __name__ == "__main__":
    main()
