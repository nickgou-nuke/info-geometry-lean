from itertools import product
import sympy as sp


def occupied_integer(modes, bits):
    out = 1
    for p, bit in zip(modes, bits):
        if bit:
            out *= p
    return out


def selected_weight_product(modes, bits, weight):
    out = 1
    for p, bit in zip(modes, bits):
        if bit:
            out *= weight(p)
    return out


def parity(bits):
    return (-1) ** sum(bits)


s = sp.symbols("s")
modes = [2, 3, 5, 7]
weight = lambda n: sp.Pow(n, -s, evaluate=False)

for bits in product((0, 1), repeat=len(modes)):
    n = occupied_integer(modes, bits)
    lhs = selected_weight_product(modes, bits, weight)
    rhs = weight(n)
    assert sp.simplify(lhs - rhs) == 0

dirichlet_word_sum = sp.expand(
    sum(
        parity(bits) * weight(occupied_integer(modes, bits))
        for bits in product((0, 1), repeat=len(modes))
    )
)
euler_superdeterminant = sp.expand(sp.prod(1 - weight(p) for p in modes))

assert sp.simplify(dirichlet_word_sum - euler_superdeterminant) == 0

print("FiniteDirichletOccupation.py: selected weights equal Dirichlet weights of occupied integers")
