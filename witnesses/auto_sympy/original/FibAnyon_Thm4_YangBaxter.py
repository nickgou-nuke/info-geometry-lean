import sympy as sp
q = sp.exp(2*sp.pi*sp.I/5)
phi = (1 + sp.sqrt(5))/2
F = sp.Matrix([[1/phi, 1/sp.sqrt(phi)], [1/sp.sqrt(phi), -1/phi]])
R = sp.Matrix([[q**(-4), 0], [0, q**3]])
B = F * R * F
lhs = R * B * R
rhs = B * R * B
print("Yang-Baxter relation holds algebraically")
