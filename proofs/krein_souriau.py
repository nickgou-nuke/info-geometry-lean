import sympy as sp


J = sp.Matrix([[0, -1], [1, 0]])
Jm = sp.Matrix([[0, 1], [1, 0]])
I2 = sp.eye(2)
beta = sp.symbols("beta", real=True)

assert J * J == -I2
assert Jm * Jm == I2
assert Jm * J * Jm == -J
assert sp.simplify(sp.log(sp.exp(beta**2 / 2)) - beta**2 / 2) == 0

print("krein_souriau.py: Krein and Gaussian Souriau identities verified")
