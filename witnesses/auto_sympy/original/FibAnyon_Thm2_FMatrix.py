import sympy as sp
phi = (1 + sp.sqrt(5)) / 2
F = sp.Matrix([[1/phi, 1/sp.sqrt(phi)], [1/sp.sqrt(phi), -1/phi]])
print("F^2 = I:", sp.simplify(F * F) == sp.eye(2))
print("det F =", sp.simplify(F.det()))
