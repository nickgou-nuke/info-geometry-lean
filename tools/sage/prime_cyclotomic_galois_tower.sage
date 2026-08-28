# Six-prime cyclotomic Galois-tower evidence generator.
#
# This script is NOT part of the trusted proof base.  It emits explicit
# arithmetic witness data that is independently reproved in Lean.

primes = [2, 3, 5, 7, 11, 13]

conductors = []
N = 1
for p in primes:
    assert is_prime(p)
    N *= p
    conductors.append(N)

degrees = [euler_phi(N) for N in conductors]
expected_conductors = [2, 6, 30, 210, 2310, 30030]
expected_degrees = [1, 2, 8, 48, 480, 5760]

assert conductors == expected_conductors
assert degrees == expected_degrees

for i in range(len(conductors) - 1):
    assert conductors[i + 1] % conductors[i] == 0

print("primes      =", primes)
print("conductors  =", conductors)
print("phi/degrees =", degrees)
print("terminal    =", conductors[-1])

# Cyclotomic Galois evidence: for Q(zeta_N)/Q the standard arithmetic model
# for the Galois group is (Z/NZ)^x, whose order is phi(N).
for N, d in zip(conductors, degrees):
    U = Integers(N).unit_group()
    assert U.order() == d
    print("N =", N, "| (Z/NZ)^x | =", U.order(), "invariants =", U.invariants())
