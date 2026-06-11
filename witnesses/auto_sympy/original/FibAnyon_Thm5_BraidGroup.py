import sympy as sp
q = sp.exp(2*sp.pi*sp.I/5)
phi = (1 + sp.sqrt(5))/2
F = sp.Matrix([[1/phi, 1/sp.sqrt(phi)], [1/sp.sqrt(phi), -1/phi]])
R = sp.Matrix([[q**(-4), 0], [0, q**3]])
B = F * R * F
b1, b2, b3 = R, B, R
print("b1 b3 = b3 b1:", sp.simplify(b1*b3 - b3*b1) == sp.zeros(2))
print("Original witness: checked one far-commutativity matrix identity; no full B4 representation proof")
