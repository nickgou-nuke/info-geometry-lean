import itertools
import sympy as sp


beta = sp.symbols("beta", positive=True)
p, q = sp.symbols("p q", positive=True, integer=True)


def fermion_prime_boltzmann_weight(prime, inv_temp):
    return prime ** (-inv_temp)


def fermion_occupation_weight(prime, inv_temp, occupied):
    return fermion_prime_boltzmann_weight(prime, inv_temp) if occupied else 1


assert fermion_occupation_weight(p, beta, False) == 1
assert fermion_occupation_weight(p, beta, True) == fermion_prime_boltzmann_weight(p, beta)

single = sum(fermion_occupation_weight(p, beta, occupied) for occupied in [False, True])
assert sp.simplify(single - (1 + fermion_prime_boltzmann_weight(p, beta))) == 0

x = sp.symbols("x")
assert sp.factor((1 + x) - (1 - x**2) / (1 - x)) == 0

local_factor = 1 + p ** (-beta)
local_zeta_ratio = (1 - p ** (-2 * beta)) / (1 - p ** (-beta))
assert sp.factor((local_factor - local_zeta_ratio) * (1 - p ** (-beta))) == 0

single_p = sum(fermion_occupation_weight(2, beta, occupied) for occupied in [False, True])
single_q = sum(fermion_occupation_weight(3, beta, occupied) for occupied in [False, True])
two_prime_sum = sum(
    fermion_occupation_weight(2, beta, bp) * fermion_occupation_weight(3, beta, bq)
    for bp, bq in itertools.product([False, True], repeat=2)
)
assert sp.simplify(single_p * single_q - two_prime_sum) == 0

expanded = (
    1
    + fermion_prime_boltzmann_weight(2, beta)
    + fermion_prime_boltzmann_weight(3, beta)
    + fermion_prime_boltzmann_weight(2, beta) * fermion_prime_boltzmann_weight(3, beta)
)
assert sp.simplify(two_prime_sum - expanded) == 0

primes = [2, 3, 5]
finite_product = sp.prod(1 + fermion_prime_boltzmann_weight(prime, beta) for prime in primes)
occupation_sum = sum(
    sp.prod(
        fermion_prime_boltzmann_weight(prime, beta) if occupied else 1
        for prime, occupied in zip(primes, occupations)
    )
    for occupations in itertools.product([False, True], repeat=len(primes))
)
assert sp.simplify(finite_product - occupation_sum) == 0

finite_zeta_ratio = sp.prod(
    (1 - prime ** (-2 * beta)) / (1 - prime ** (-beta)) for prime in primes
)
denominator = sp.prod(1 - prime ** (-beta) for prime in primes)
assert sp.factor((finite_product - finite_zeta_ratio) * denominator) == 0

print("FermionicPrimonPartition.py: finite fermionic Euler product verified")
