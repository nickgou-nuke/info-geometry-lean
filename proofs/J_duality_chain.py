import sympy as sp


J = sp.Matrix([[0, 1], [1, 0]])
Jc = sp.Matrix([[0, -1], [1, 0]])
Gamma = sp.Matrix([[1, 0], [0, -1]])
I2 = sp.eye(2)

assert J * J == I2
assert Jc * Jc == -I2
assert J * Jc * J == -Jc
assert Gamma * Gamma == I2
assert J * Gamma == -(Gamma * J)

x, p = sp.symbols("x p", real=True)
Phi = x**2 / 2
dual_objective = p * x - Phi
critical_x = sp.solve(sp.diff(dual_objective, x), x)[0]
dual_value = sp.simplify(dual_objective.subs(x, critical_x))
assert sp.simplify(dual_value - p**2 / 2) == 0
assert sp.simplify(x**2 / 2 + p**2 / 2 - x * p - (p - x) ** 2 / 2) == 0

z = sp.symbols("z", nonzero=True)
assert sp.simplify(1 / (1 / z) - z) == 0

print("J_duality_chain.py: V4 and quadratic Fenchel identities verified")
