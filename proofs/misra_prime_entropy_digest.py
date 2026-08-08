#!/usr/bin/env python3
"""Finite witness for MisraPrimeEntropyDigest.lean.

Checks only the finite arithmetic of the entropy proxy E_1(n)=n/pi_1(n), where
pi_1 counts ordinary primes plus the convention that 1 is prime-like.  This does
not prove RH, P!=NP, or twin primes.
"""

from fractions import Fraction
import sympy as sp


def misra_prime_like(n: int) -> bool:
    return n == 1 or sp.isprime(n)


def pi_one(n: int) -> int:
    return sum(1 for k in range(n + 1) if misra_prime_like(k))


def entropy(n: int) -> Fraction:
    return Fraction(n, pi_one(n))

assert not sp.isprime(1)
assert misra_prime_like(1)
assert [pi_one(n) for n in [1, 10, 11, 12, 13, 14]] == [1, 5, 6, 6, 7, 7]
assert [entropy(n) for n in [1, 10, 11, 12, 13, 14]] == [
    Fraction(1, 1),
    Fraction(2, 1),
    Fraction(11, 6),
    Fraction(2, 1),
    Fraction(13, 7),
    Fraction(2, 1),
]
assert entropy(11) < entropy(10)
assert entropy(10) == entropy(12) == entropy(14)

# Compare with log n heuristic from PNT: n/pi(n) is roughly log n at moderate scale.
for n in [100, 1000, 10000]:
    ratio = float(entropy(n)) / float(sp.log(n))
    assert 0.7 < ratio < 1.4

print("misra_prime_entropy_digest.py: finite witnesses passed")
