import sympy as sp

Z = sp.Integer


def em_pi_order(group_order, k, n):
    return Z(group_order) if k == n else Z(1)


def is_trivial_pi(group_order, k, n):
    return em_pi_order(group_order, k, n) == 1


assert em_pi_order(7, 3, 3) == 7
assert is_trivial_pi(7, 2, 3)
assert is_trivial_pi(7, 4, 3)


def product_pi_order(g_order, h_order, k):
    return em_pi_order(g_order, k, 1) * em_pi_order(h_order, k, 2)


assert product_pi_order(5, 11, 1) == 5
assert product_pi_order(5, 11, 2) == 11
assert product_pi_order(5, 11, 3) == 1


def reduced_sphere_cohomology_rank(k, n):
    return 1 if k == n else 0


assert reduced_sphere_cohomology_rank(4, 4) == 1
assert reduced_sphere_cohomology_rank(3, 4) == 0
assert reduced_sphere_cohomology_rank(5, 4) == 0


def suspension_shift_index(k):
    return k + 1


assert suspension_shift_index(1) == 2
assert suspension_shift_index(2) == 3


def freudenthal_stable(n, k):
    return k <= 2 * n - 2


assert freudenthal_stable(2, 2)
assert freudenthal_stable(3, 4)
assert not freudenthal_stable(2, 3)

n, k, g = sp.symbols("n k g", integer=True, positive=True)
diagonal = sp.Eq(k, n)
assert sp.simplify((k + 1) - (n + 1) - (k - n)) == 0

print({
    "pi_K_Z7_3_at_3": em_pi_order(7, 3, 3),
    "pi_K_Z7_3_at_2": em_pi_order(7, 2, 3),
    "product_pi1": product_pi_order(5, 11, 1),
    "product_pi2": product_pi_order(5, 11, 2),
    "Htilde_S4_degree4_rank": reduced_sphere_cohomology_rank(4, 4),
})
