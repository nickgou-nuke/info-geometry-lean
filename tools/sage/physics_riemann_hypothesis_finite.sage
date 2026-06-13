# SageMath finite verifier for arXiv:1101.3116v1.
# Run with:
#   /home/goutev/miniforge3/envs/sage/bin/sage tools/sage/physics_riemann_hypothesis_finite.sage
#
# This is finite exact arithmetic only.  It verifies polynomial/product
# identities and Mobius/divisor finite data; it does not prove RH or any
# analytic/physical spectral assertion.

from sage.all import QQ, factor, prime_pi, divisors, moebius


def mobius_definition(n):
    if n == 1:
        return 1
    fac = factor(n)
    for _, exp in fac:
        if exp > 1:
            return 0
    return -1 if len(fac) % 2 else 1


def finite_euler_product(primes, k, bound):
    total = QQ(1)
    for p in primes:
        total *= sum(QQ(1) / QQ(p) ** (k * a) for a in range(bound + 1))
    return total


def finite_smooth_sum(primes, k, bound):
    terms = [QQ(1)]
    for p in primes:
        terms = [term * QQ(1) / QQ(p) ** (k * a) for term in terms for a in range(bound + 1)]
    return sum(terms, QQ(0))


primes = [2, 3]
k = 2
bound = 3
lhs = finite_euler_product(primes, k, bound)
rhs = finite_smooth_sum(primes, k, bound)
assert lhs == rhs
assert lhs == QQ(17425) / QQ(11664)

for p in [2, 3, 5, 7, 11, 13]:
    factor_value = QQ(1) - QQ(1) / QQ(p) ** 2
    assert factor_value != 0
    assert factor_value > 0

signed_mobius = QQ(1)
bosonic = QQ(1)
for p in primes:
    signed_mobius *= QQ(1) - QQ(1) / QQ(p) ** 2
    bosonic *= QQ(1) / (QQ(1) - QQ(1) / QQ(p) ** 2)
assert signed_mobius == QQ(2) / QQ(3)
assert bosonic == QQ(3) / QQ(2)
assert bosonic * signed_mobius == QQ(1)

finite_fermion = QQ(1)
finite_parafermion3 = QQ(1)
quotient_fermion = QQ(1)
quotient_parafermion3 = QQ(1)
for p in primes:
    finite_fermion *= sum(QQ(1) / QQ(p) ** (2 * a) for a in range(2))
    finite_parafermion3 *= sum(QQ(1) / QQ(p) ** (2 * a) for a in range(3))
    quotient_fermion *= (QQ(1) - QQ(1) / QQ(p) ** 4) / (QQ(1) - QQ(1) / QQ(p) ** 2)
    quotient_parafermion3 *= (QQ(1) - QQ(1) / QQ(p) ** 6) / (QQ(1) - QQ(1) / QQ(p) ** 2)
assert finite_fermion == quotient_fermion == QQ(25) / QQ(18)
assert finite_parafermion3 == quotient_parafermion3 == QQ(637) / QQ(432)

for n in range(1, 101):
    assert mobius_definition(n) == moebius(n)
    divisor_sum = sum(mobius_definition(d) for d in divisors(n))
    assert divisor_sum == (1 if n == 1 else 0)

for n in [4, 8, 9, 12, 16, 18, 20, 24, 25, 27, 28, 36]:
    assert mobius_definition(n) == 0

expected_pi = {10: 4, 30: 10, 100: 25, 200: 46}
for limit, expected in expected_pi.items():
    assert prime_pi(limit) == expected

mertens = {n: sum(mobius_definition(j) for j in range(1, n + 1)) for n in range(1, 51)}
assert mertens[1] == 1
assert mertens[10] == -1
assert mertens[50] == -3

print("physics_rh_finite: all exact Sage assertions passed")
print("finite_euler_2_3_k2_B3 =", lhs)
print("finite_primon_boson_x_signed_mobius =", bosonic * signed_mobius)
print("finite_fermion_primon_Z2_over_2_3_s2 =", finite_fermion)
print("finite_parafermion_kappa3_over_2_3_s2 =", finite_parafermion3)
print("scope: finite arithmetic only; no RH / Hilbert-Polya / analytic-continuation proof")
