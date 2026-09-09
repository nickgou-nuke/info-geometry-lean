#!/usr/bin/env sage
"""Exact finite certificate for the cumulative cyclotomic Galois tower."""

from math import gcd

PRIMES = [2, 3, 5, 7, 11, 13]
MODULI = []
m = 1
for p in PRIMES:
    m *= p
    MODULI.append(m)

def units(n):
    return [a for a in range(n) if gcd(a, n) == 1]

assert all(MODULI[i] < MODULI[i+1] for i in range(5))
assert all(MODULI[i] | MODULI[i+1] for i in range(5))

for i, n in enumerate(MODULI):
    U = units(n)
    assert len(U) == euler_phi(n)
    assert all((a * b) % n in U for a in U for b in U)
    assert all(pow(a, euler_phi(n), n) == 1 for a in U)

for i in range(5):
    low, high = MODULI[i], MODULI[i+1]
    U_low, U_high = units(low), units(high)
    restriction = {a: a % low for a in U_high}
    assert set(restriction.values()) == set(U_low)
    assert len(U_high) == len(U_low) * (len([a for a in U_high if a % low == 1]))
    assert len([a for a in U_high if a % low == 1]) == euler_phi(high) // euler_phi(low)

for i in range(4):
    a, b, c = MODULI[i], MODULI[i+1], MODULI[i+2]
    for x in units(c):
        assert (x % b) % a == x % a

print("PRIME_CYCLOTOMIC_GALOIS_TOWER")
print("primes=", PRIMES)
print("moduli=", MODULI)
print("degrees=", [euler_phi(n) for n in MODULI])
print("restriction_maps=surjective")
print("restriction_composition=verified")
print("STATUS=PASS")

