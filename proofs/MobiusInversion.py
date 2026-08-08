from sympy.functions.combinatorial.numbers import mobius
from sympy.ntheory import divisors


def dirichlet_convolution(f, g, n):
    return sum(f(d) * g(n // d) for d in divisors(n))


def zeta_kernel(_n):
    return 1


def vacuum_kernel(n):
    return 1 if n == 1 else 0


def mobius_kernel(n):
    return int(mobius(n))


for n in range(1, 41):
    assert dirichlet_convolution(zeta_kernel, mobius_kernel, n) == vacuum_kernel(n)
    assert dirichlet_convolution(mobius_kernel, zeta_kernel, n) == vacuum_kernel(n)


def f(n):
    return n * n - 3 * n + 2


def g(n):
    return dirichlet_convolution(f, zeta_kernel, n)


for n in range(1, 41):
    recovered = dirichlet_convolution(g, mobius_kernel, n)
    assert recovered == f(n)

print("MobiusInversion.py: Dirichlet convolution and Möbius inversion verified")
