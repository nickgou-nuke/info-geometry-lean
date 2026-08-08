import sympy as sp


E = sp.Matrix([[1, 0], [0, -1]])
F = sp.Matrix([[0, 1], [1, 0]])
I2 = sp.eye(2)
P = E * F

assert E * E == I2
assert F * F == I2
assert E * F + F * E == sp.zeros(2)
assert P * P == -I2
assert E.det() == -1
assert F.det() == -1
assert P.det() == 1

n = sp.symbols("n", integer=True, nonnegative=True)
assert sp.simplify(2 ** (n + 1) - 2 * 2**n) == 0

print("uhf_ladder.py: Clifford seed and UHF dimension identities verified")
