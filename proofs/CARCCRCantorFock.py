import sympy as sp


# CAR one-mode seed: a^2 = 0, (a†)^2 = 0, a a† + a† a = I.
a = sp.Matrix([[0, 1], [0, 0]])
adag = sp.Matrix([[0, 0], [1, 0]])
I2 = sp.eye(2)

assert a * a == sp.zeros(2)
assert adag * adag == sp.zeros(2)
assert a * adag + adag * a == I2

number = adag * a
parity = I2 - 2 * number

assert number * number == number
assert parity * parity == I2
assert parity * a == -a * parity
assert parity * adag == -adag * parity


# CCR finite truncation witness.  Exact CCR cannot hold in finite dimension:
# trace([a,a†]) = 0, while trace(I) = dimension.  The truncated oscillator has
# a boundary anomaly on the top occupation state.
def truncated_annihilation(K):
    dim = K + 1
    A = sp.zeros(dim)
    for n in range(1, dim):
        A[n - 1, n] = sp.sqrt(n)
    return A


def truncated_creation(K):
    return truncated_annihilation(K).T


K = 5
b = truncated_annihilation(K)
bdag = truncated_creation(K)
comm = sp.simplify(b * bdag - bdag * b)
expected = sp.diag(*([1] * K + [-K]))

assert comm == expected
assert sp.trace(comm) == 0


# Cantor/CAR versus Baire/CCR occupation spaces.
def car_words(n):
    if n == 0:
        return [()]
    return [(bit,) + tail for bit in (False, True) for tail in car_words(n - 1)]


def ccr_words(n, cutoff):
    if n == 0:
        return [()]
    return [(k,) + tail for k in range(cutoff + 1) for tail in ccr_words(n - 1, cutoff)]


assert len(car_words(4)) == 2**4
assert len(ccr_words(3, 5)) == 6**3

x0, x1, x2 = sp.symbols("x0 x1 x2")
xs = [x0, x1, x2]

car_ordinary = sp.expand(sp.prod(1 + x for x in xs))
car_graded = sp.expand(sp.prod(1 - x for x in xs))
ccr_truncated = sp.expand(sp.prod(sum(x**k for k in range(4)) for x in xs))
ccr_formal = sp.prod(1 / (1 - x) for x in xs)

assert sp.simplify(ccr_formal * car_graded) == 1
assert car_ordinary == sp.expand(sum(
    sp.prod(x for bit, x in zip(word, xs) if bit)
    for word in car_words(len(xs))
))
assert ccr_truncated == sp.expand(sum(
    sp.prod(x**k for k, x in zip(word, xs))
    for word in ccr_words(len(xs), 3)
))

print("CARCCRCantorFock.py: CAR seed, CCR truncation, and Cantor/Baire Fock factors verified")
