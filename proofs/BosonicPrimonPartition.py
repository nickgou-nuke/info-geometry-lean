import sympy as sp


beta = sp.symbols("beta", positive=True)
p, q = sp.symbols("p q", positive=True, integer=True)
K = sp.symbols("K", integer=True, nonnegative=True)


def prime_boltzmann_weight(prime, inv_temp):
    return prime ** (-inv_temp)


def boson_occupation_weight(prime, inv_temp, occupation):
    return prime_boltzmann_weight(prime, inv_temp) ** occupation


assert boson_occupation_weight(p, beta, 0) == 1

k = sp.symbols("k", integer=True, nonnegative=True)
assert sp.simplify(
    boson_occupation_weight(p, beta, k + 1)
    - boson_occupation_weight(p, beta, k) * prime_boltzmann_weight(p, beta)
) == 0

for cutoff in range(0, 6):
    left = sum(boson_occupation_weight(2, beta, k) for k in range(cutoff + 1))
    right = sum(boson_occupation_weight(2, beta, k) for k in range(cutoff))
    if cutoff > 0:
        assert sp.simplify(left - right - boson_occupation_weight(2, beta, cutoff)) == 0

for cutoff in range(0, 6):
    single_p = sum(boson_occupation_weight(2, beta, k) for k in range(cutoff + 1))
    single_q = sum(boson_occupation_weight(3, beta, l) for l in range(cutoff + 1))
    two_prime_sum = sum(
        boson_occupation_weight(2, beta, k) * boson_occupation_weight(3, beta, l)
        for k in range(cutoff + 1)
        for l in range(cutoff + 1)
    )
    assert sp.simplify(single_p * single_q - two_prime_sum) == 0

x = sp.symbols("x")
for cutoff in range(0, 8):
    closed_single = sum(x**k for k in range(cutoff + 1))
    geometric_closed = (1 - x ** (cutoff + 1)) / (1 - x)
    assert sp.factor((closed_single - geometric_closed) * (1 - x)) == 0

print("BosonicPrimonPartition.py: finite bosonic Euler product verified")
