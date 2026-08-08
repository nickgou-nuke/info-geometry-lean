import sympy as sp


sx = sp.Matrix([[0, 1], [1, 0]])
sy = sp.Matrix([[0, 1], [-1, 0]])
I2 = sp.eye(2)

assert sx * sx == I2
assert sy * sy == -I2
assert sx * sy == -(sy * sx)

x, y = sp.symbols("x y", real=True)
F = x * sx + y * sy
assert sp.simplify(F * F - (x**2 - y**2) * I2) == sp.zeros(2)

a, b, c, d = sp.symbols("a b c d", real=True)
M = sp.Matrix([[a, b], [c, d]])
basis_reconstruction = (
    (a + d) / 2 * I2
    + (b + c) / 2 * sx
    + (b - c) / 2 * sy
    + (d - a) / 2 * (sx * sy)
)
assert sp.simplify(M - basis_reconstruction) == sp.zeros(2)

print("clifford_seed.py: Cl(1,1) matrix seed identities verified")
