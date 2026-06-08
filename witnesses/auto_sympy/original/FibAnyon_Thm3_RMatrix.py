import sympy as sp
q = sp.exp(2*sp.pi*sp.I/5)
R = sp.Matrix([[q**(-4), 0], [0, q**3]])
print("det R = q^-1:", sp.simplify(R.det() - q**(-1)) == 0)
print("q^5 =", sp.simplify(q**5))
print("R unitary:", sp.simplify(R.H * R) == sp.eye(2))
