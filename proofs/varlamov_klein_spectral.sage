var("d k")

tripotent_roots = solve(d^3 == d, d)
root_values = sorted([r.rhs() for r in tripotent_roots])

su5_adjoint_dim = 5^2 - 1
spinor_dim = 2^5
varlamov_even = sum(binomial(5, i) for i in [0, 2, 4])
varlamov_odd = sum(binomial(5, i) for i in [1, 3, 5])
witten_moebius_index = varlamov_even - varlamov_odd
W_A4 = WeylGroup(["A", 4])
mobius_action = PermutationGroup([[(1, 2)]])

assert su5_adjoint_dim == 24
assert spinor_dim == 32
assert varlamov_even == 16
assert varlamov_odd == 16
assert varlamov_even + varlamov_odd == spinor_dim
assert witten_moebius_index == 0
assert root_values == [-1, 0, 1]
assert -(-k) == k
assert W_A4.order() == 120
assert mobius_action.order() == 2

print({
    "su5_adjoint_dim": su5_adjoint_dim,
    "spinor_dim": spinor_dim,
    "varlamov_even": varlamov_even,
    "varlamov_odd": varlamov_odd,
    "witten_moebius_index": witten_moebius_index,
    "tripotent_roots": root_values,
    "weyl_A4_order": W_A4.order(),
    "mobius_group_order": mobius_action.order(),
    "edges": 6,
})
