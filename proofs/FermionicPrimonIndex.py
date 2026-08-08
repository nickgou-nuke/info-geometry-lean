import sympy as sp


x, c, s, s0 = sp.symbols("x c s s0")


def bosonic_local_factor(weight):
    return 1 / (1 - weight)


def ordinary_fermion_local_factor(weight):
    return 1 + weight


def graded_fermion_local_factor(weight):
    return 1 - weight


# Ordinary fermion: local factor in ζ(s)/ζ(2s).
ordinary_ratio_identity = (
    ordinary_fermion_local_factor(x) - (1 - x**2) / (1 - x)
) * (1 - x)
assert sp.factor(ordinary_ratio_identity) == 0

# Graded index: local cancellation with the bosonic Euler factor.
graded_cancellation = (
    bosonic_local_factor(x) * graded_fermion_local_factor(x) - 1
) * (1 - x)
assert sp.factor(graded_cancellation) == 0

# Simple zero local model: ζ(s) ~ c(s-s0) implies 1/ζ(s) ~ 1/(c(s-s0)).
simple_zero_model = 1 / (c * (s - s0)) - (1 / c) * (1 / (s - s0))
assert sp.factor(simple_zero_model * c * (s - s0)) == 0

# Bosonic pole at s=1 is canceled by the reciprocal graded zero model s-1.
bosonic_pole_model = 1 / (s - 1)
graded_zero_model = s - 1
assert sp.factor(bosonic_pole_model * graded_zero_model - 1) == 0

# Finite product distinction over a few prime modes.
beta = sp.symbols("beta", positive=True)
primes = [2, 3, 5]
weights = [p ** (-beta) for p in primes]

ordinary_product = sp.prod(ordinary_fermion_local_factor(w) for w in weights)
ordinary_zeta_ratio_product = sp.prod((1 - w**2) / (1 - w) for w in weights)
ordinary_denominator = sp.prod(1 - w for w in weights)
assert sp.factor((ordinary_product - ordinary_zeta_ratio_product) * ordinary_denominator) == 0

graded_product = sp.prod(graded_fermion_local_factor(w) for w in weights)
bosonic_product = sp.prod(bosonic_local_factor(w) for w in weights)
assert sp.factor((bosonic_product * graded_product - 1) * ordinary_denominator) == 0

print("FermionicPrimonIndex.py: ordinary fermion vs graded index identities verified")
