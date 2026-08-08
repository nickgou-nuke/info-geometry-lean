from itertools import product
import sympy as sp


def boolean_words(n):
    return product((0, 1), repeat=n)


def parity(word):
    return (-1) ** sum(word)


def occupied_integer(word, primes):
    out = 1
    for bit, p in zip(word, primes):
        if bit:
            out *= p
    return out


def finite_arithmetic_supertrace(primes, s):
    total = 0
    for word in boolean_words(len(primes)):
        n = occupied_integer(word, primes)
        total += parity(word) * sp.Pow(n, -s, evaluate=False)
    return sp.expand(total)


def finite_euler_superdeterminant(primes, s):
    return sp.expand(sp.prod(1 - sp.Pow(p, -s, evaluate=False) for p in primes))


s = sp.symbols("s")
primes = [2, 3, 5, 7]

assert sp.simplify(
    finite_arithmetic_supertrace(primes, s)
    - finite_euler_superdeterminant(primes, s)
) == 0

# Adding one prime appends one local graded Euler factor.
old = finite_arithmetic_supertrace(primes[:-1], s)
new = finite_arithmetic_supertrace(primes, s)
assert sp.simplify(new - old * (1 - sp.Pow(7, -s, evaluate=False))) == 0

# The integer support is squarefree in the cutoff primes.
coefficients = {
    occupied_integer(word, primes): parity(word)
    for word in boolean_words(len(primes))
}

assert coefficients[1] == 1
assert coefficients[2] == -1
assert coefficients[2 * 3] == 1
assert coefficients[2 * 3 * 5] == -1
assert coefficients[2 * 3 * 5 * 7] == 1

print("FiniteArithmeticUHFTrace.py: finite arithmetic UHF supertrace equals Euler superdeterminant")
