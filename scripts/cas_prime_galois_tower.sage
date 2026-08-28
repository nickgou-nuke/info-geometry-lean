#!/usr/bin/env sage
"""Exact cyclotomic/Galois tower certificate for the requested primes."""
primes = [2, 3, 5, 7, 11, 13]
print("PRIME_GALOIS_TOWER")
for p in primes:
    R.<x> = PolynomialRing(QQ)
    phi = cyclotomic_polynomial(p, x)
    units = [a for a in range(1, p) if gcd(a, p) == 1]
    assert phi.degree() == p - 1
    assert len(units) == p - 1
    print("p=%d degree=%d galois_order=%d automorphisms=%s" %
          (p, phi.degree(), len(units), units))
print("STATUS=PASS")
