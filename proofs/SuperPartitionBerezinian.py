import sympy as sp


x, eps, y = sp.symbols("x eps y")

bosonic_local_factor = 1 / (1 - x)
fermionic_local_factor = 1 + x
super_partition_ratio = fermionic_local_factor / (1 - x)
cayley_partition = (1 + x) / (1 - x)

assert sp.simplify(super_partition_ratio - cayley_partition) == 0
assert sp.simplify(fermionic_local_factor * bosonic_local_factor - super_partition_ratio) == 0


def diagonal_berezinian(even, odd):
    return even / odd


assert sp.simplify(
    super_partition_ratio - diagonal_berezinian(1 + x, 1 - x)
) == 0

assert sp.simplify(cayley_partition.subs(x, -x) - 1 / cayley_partition) == 0

exp_chart = sp.exp(eps * y)
exponential_cayley = cayley_partition.subs(x, exp_chart)
assert sp.simplify(
    exponential_cayley - diagonal_berezinian(1 + exp_chart, 1 - exp_chart)
) == 0
assert sp.exp(0) == 1

weights = sp.symbols("x0 x1 x2")
bosonic_product = sp.prod(1 / (1 - w) for w in weights)
fermionic_product = sp.prod(1 + w for w in weights)
super_product = fermionic_product * bosonic_product
berezinian_product = sp.prod(diagonal_berezinian(1 + w, 1 - w) for w in weights)
assert sp.simplify(super_product - berezinian_product) == 0

print("SuperPartitionBerezinian.py: super-ratio, Berezinian, and Cayley chart verified")
