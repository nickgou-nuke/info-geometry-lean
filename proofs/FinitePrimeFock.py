from itertools import product
import sympy as sp


def fermion_configs(m):
    return product((0, 1), repeat=m)


def occupation_energy(config, log_primes):
    return sum(k * lp for k, lp in zip(config, log_primes))


def fermion_parity(config):
    return (-1) ** sum(config)


def graded_fock_supertrace(xs):
    total = 0
    for config in fermion_configs(len(xs)):
        weight = 1
        for k, x in zip(config, xs):
            if k:
                weight *= x
        total += fermion_parity(config) * weight
    return sp.expand(total)


def ordinary_fermion_trace(xs):
    total = 0
    for config in fermion_configs(len(xs)):
        weight = 1
        for k, x in zip(config, xs):
            if k:
                weight *= x
        total += weight
    return sp.expand(total)


x2, x3, x5, x7 = sp.symbols("x2 x3 x5 x7")
xs = [x2, x3, x5, x7]

graded_product = sp.expand(sp.prod(1 - x for x in xs))
ordinary_product = sp.expand(sp.prod(1 + x for x in xs))
bosonic_product = sp.prod(1 / (1 - x) for x in xs)

assert graded_fock_supertrace(xs) == graded_product
assert ordinary_fermion_trace(xs) == ordinary_product
assert sp.simplify(bosonic_product * graded_product) == 1

# Arithmetic specialization x_p = p^{-s}.
s = sp.symbols("s")
primes = [2, 3, 5, 7]
arith_xs = [sp.Pow(p, -s, evaluate=False) for p in primes]

finite_mobius_index = graded_fock_supertrace(arith_xs)
finite_euler_factor = sp.expand(sp.prod(1 - x for x in arith_xs))

assert sp.simplify(finite_mobius_index - finite_euler_factor) == 0

# The squarefree support appears explicitly: every occupied prime is used once.
terms = {}
for config in fermion_configs(len(primes)):
    n = sp.prod(p for k, p in zip(config, primes) if k)
    terms[n] = fermion_parity(config)

assert terms[1] == 1
assert terms[2] == -1
assert terms[2 * 3] == 1
assert terms[2 * 3 * 5] == -1
assert terms[2 * 3 * 5 * 7] == 1

print("FinitePrimeFock.py: finite Fock supertrace and Euler cancellation verified")
