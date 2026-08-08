from sympy import factorint
from sympy.functions.combinatorial.numbers import mobius
from sympy.ntheory import primerange


def is_squarefree(n):
    return all(exp == 1 for exp in factorint(n).values())


def fermion_parity(n):
    return int(mobius(n))


def parity_from_distinct_primes(n):
    return (-1) ** len(factorint(n))


for n in range(1, 80):
    if is_squarefree(n):
        assert fermion_parity(n) == parity_from_distinct_primes(n)
    else:
        assert fermion_parity(n) == 0

for p in primerange(2, 80):
    assert fermion_parity(p) == -1


def dirichlet_convolution(f, g, n):
    return sum(f(d) * g(n // d) for d in range(1, n + 1) if n % d == 0)


def zeta_kernel(_n):
    return 1


def vacuum_kernel(n):
    return 1 if n == 1 else 0


for n in range(1, 80):
    assert dirichlet_convolution(zeta_kernel, fermion_parity, n) == vacuum_kernel(n)
    assert dirichlet_convolution(fermion_parity, zeta_kernel, n) == vacuum_kernel(n)

print("PrimonZetaMobius.py: Möbius parity and zeta cancellation verified")
