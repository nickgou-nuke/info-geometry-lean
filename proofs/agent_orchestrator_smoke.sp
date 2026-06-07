import sympy as sp
n = sp.symbols("n", integer=True, nonnegative=True)
assert sp.simplify(n + 0 - n) == 0
print("sympy_ok: n + 0 = n")
