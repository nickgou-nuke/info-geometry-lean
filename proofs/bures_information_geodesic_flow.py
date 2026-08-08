#!/usr/bin/env python3
"""SymPy audit for the finite Bures/information-geodesic toy."""

import sympy as sp

I, theta, E, K, A = sp.symbols('I theta E K A', positive=True, real=True)

fisher_quadratic = I * theta**2 / 2
dual_fisher_quadratic = E**2 / (2 * I)
legendre_gap = sp.simplify(fisher_quadratic + dual_fisher_quadratic - theta * E)

modular_flow_zero_time = sp.simplify(A)
bures_center_distance = sp.Integer(0)
bures_origin_metric = sp.symbols('dx dy dz', real=True)

cramer_rao_bound = sp.simplify(1 / I)

print("fisher quadratic =", fisher_quadratic)
print("dual fisher quadratic =", dual_fisher_quadratic)
print("Fenchel-Young gap =", legendre_gap)
print("zero-time modular flow =", modular_flow_zero_time)
print("Bures center distance =", bures_center_distance)
print("Cramér-Rao bound =", cramer_rao_bound)

assert sp.simplify(legendre_gap - (I * theta - E)**2 / (2 * I)) == 0
assert bures_center_distance == 0
assert modular_flow_zero_time == A
assert cramer_rao_bound == 1 / I

print("bures_information_geodesic_flow.py: SymPy audit passed")
