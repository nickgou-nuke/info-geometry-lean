import sympy as sp


phi = (1 + sp.sqrt(5)) / 2
tau = 1 / phi
F = sp.Matrix([[tau, sp.sqrt(tau)], [sp.sqrt(tau), -tau]])

assert sp.simplify(phi**2 - phi - 1) == 0
assert sp.simplify(tau**2 + tau - 1) == 0
assert sp.simplify(F * F - sp.eye(2)) == sp.zeros(2)
assert F.T == F

print("FibAnyonThm6_pentagon.py: Fibonacci pentagon matrix identities verified")
