import sympy as sp
n = sp.symbols('n', integer=True, nonnegative=True)
assert sp.simplify(0 + n - n) == 0
print('sympy_ok: 0 + n = n')
