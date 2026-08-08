import sympy as sp


Jc = sp.Matrix([[0, -1], [1, 0]])
eta = sp.Matrix([[1, 0], [0, -1]])
Jm = sp.Matrix([[0, 1], [1, 0]])
I2 = sp.eye(2)
beta, K, t = sp.symbols("beta K t", real=True)

assert Jc * Jc == -I2
assert eta * eta == I2
assert eta * Jc * eta == -Jc
assert Jm * Jm == I2
assert Jm * Jc * Jm == -Jc
assert sp.simplify(sp.log(sp.exp(beta**2 / 2)) - beta**2 / 2) == 0

left_arg = sp.expand(-sp.I * K * (t + beta))
split_arg = sp.expand(-sp.I * K * t + -sp.I * K * beta)
assert sp.simplify(left_arg - split_arg) == 0

print("krein_souriau_full.py: Krein/Souriau/metriplectic seed identities verified")
