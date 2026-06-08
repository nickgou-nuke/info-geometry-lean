import sympy as sp
phi = (1 + sp.sqrt(5)) / 2
tau = (1 - sp.sqrt(5)) / 2
print("phi^2 = phi + 1:", sp.simplify(phi**2 - phi - 1) == 0)
print("tau^2 + tau = 1:", sp.simplify(tau**2 + tau - 1) == 0)
