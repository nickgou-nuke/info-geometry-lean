from itertools import product
import sympy as sp


def occupation_words(n):
    return list(product((0, 1), repeat=n))


def occupied_count(word):
    return sum(word)


def word_weight(word, xs):
    out = 1
    for bit, x in zip(word, xs):
        if bit:
            out *= x
    return out


def word_mobius_sign(word):
    return (-1) ** occupied_count(word)


def finite_mobius_supertrace(xs):
    return sp.expand(sum(word_mobius_sign(w) * word_weight(w, xs) for w in occupation_words(len(xs))))


def squarefree_integer_from_word(word, primes):
    out = 1
    for bit, p in zip(word, primes):
        if bit:
            out *= p
    return out


x2, x3, x5, x7 = sp.symbols("x2 x3 x5 x7")
xs = [x2, x3, x5, x7]

assert finite_mobius_supertrace(xs) == sp.expand(sp.prod(1 - x for x in xs))

primes = [2, 3, 5, 7]
coefficients = {}
for word in occupation_words(len(primes)):
    n = squarefree_integer_from_word(word, primes)
    coefficients[n] = word_mobius_sign(word)

assert coefficients[1] == 1
assert coefficients[2] == -1
assert coefficients[3] == -1
assert coefficients[2 * 3] == 1
assert coefficients[2 * 3 * 5] == -1
assert coefficients[2 * 3 * 5 * 7] == 1

s = sp.symbols("s")
dirichlet_supertrace = sp.expand(
    sum(sign * sp.Pow(n, -s, evaluate=False) for n, sign in coefficients.items())
)
euler_superdeterminant = sp.expand(sp.prod(1 - sp.Pow(p, -s, evaluate=False) for p in primes))

assert sp.simplify(dirichlet_supertrace - euler_superdeterminant) == 0

print("FiniteMobiusCoefficient.py: finite Mobius coefficients extracted from Fock words")
