import sympy as sp


x, y, p = sp.symbols("x y p", real=True)
Phi = lambda z: z**2 / 2

fenchel_objective = p * x - Phi(x)
critical_x = sp.solve(sp.diff(fenchel_objective, x), x)[0]
fenchel_value = sp.simplify(fenchel_objective.subs(x, critical_x))
assert sp.simplify(fenchel_value - p**2 / 2) == 0

fenchel_young_gap = sp.simplify(Phi(x) + p**2 / 2 - x * p)
assert sp.simplify(fenchel_young_gap - (p - x) ** 2 / 2) == 0

bregman = sp.simplify(Phi(x) - Phi(y) - y * (x - y))
assert sp.simplify(bregman - (x - y) ** 2 / 2) == 0

grad = sp.diff(Phi(x), x)
assert sp.simplify(grad - x) == 0
assert sp.simplify(grad.subs(x, grad) - x) == 0

print("FenchelSpacetime.py: quadratic Fenchel/Bregman identities verified")
