import sympy as sp
from math import comb, factorial

d = sp.Symbol("d", integer=True)
k = sp.Symbol("k", integer=True)

tripotent_poly = d**3 - d
tripotent_roots = sp.solve(tripotent_poly, d)

su5_adjoint_dim = 5**2 - 1
spinor_dim = 2**5
varlamov_even = sum(comb(5, i) for i in [0, 2, 4])
varlamov_odd = sum(comb(5, i) for i in [1, 3, 5])
witten_moebius_index = varlamov_even - varlamov_odd
weyl_A4_order = factorial(5)
mobius_group_order = 2
mobius_inv = lambda x: -x

assert su5_adjoint_dim == 24
assert spinor_dim == 32
assert varlamov_even == 16
assert varlamov_odd == 16
assert varlamov_even + varlamov_odd == spinor_dim
assert witten_moebius_index == 0
assert set(tripotent_roots) == {-1, 0, 1}
assert sp.expand(mobius_inv(mobius_inv(k)) - k) == 0
assert weyl_A4_order == 120
assert mobius_group_order == 2

print({
    "su5_adjoint_dim": su5_adjoint_dim,
    "spinor_dim": spinor_dim,
    "varlamov_even": varlamov_even,
    "varlamov_odd": varlamov_odd,
    "witten_moebius_index": witten_moebius_index,
    "tripotent_roots": sorted(tripotent_roots),
    "weyl_A4_order": weyl_A4_order,
    "mobius_group_order": mobius_group_order,
    "edges": 6,
})
