import sympy as sp


beta, tau, q = sp.symbols("beta tau q", real=True)

I2 = sp.eye(2)
Z2 = sp.zeros(2)

elliptic_unit = sp.Matrix([[0, -1], [1, 0]])
hyperbolic_unit = sp.Matrix([[0, 1], [1, 0]])
parabolic_unit = sp.Matrix([[0, 1], [0, 0]])

assert elliptic_unit * elliptic_unit == -I2
assert hyperbolic_unit * hyperbolic_unit == I2
assert parabolic_unit * parabolic_unit == Z2

elliptic_temperature = sp.Matrix([[beta, -tau], [tau, beta]])
hyperbolic_temperature = sp.Matrix([[beta, tau], [tau, beta]])
parabolic_temperature = sp.Matrix([[beta, tau], [0, beta]])

assert sp.factor(elliptic_temperature.det() - (beta**2 + tau**2)) == 0
assert sp.factor(hyperbolic_temperature.det() - (beta**2 - tau**2)) == 0
assert sp.factor(parabolic_temperature.det() - beta**2) == 0

sector_tripotent = sp.Matrix([[q, 0], [0, 1]])
cube_minus_self = sector_tripotent**3 - sector_tripotent
assert cube_minus_self == sp.Matrix([[q**3 - q, 0], [0, 0]])
assert sp.factor(sector_tripotent.det() - q) == 0

for value, sector in [(1, "elliptic"), (0, "parabolic"), (-1, "hyperbolic")]:
    op = sector_tripotent.subs(q, value)
    assert op**3 == op
    assert op.det() == value

z = sp.symbols("z")
graded_supertrace_reciprocal = 1 / z
assert sp.simplify(graded_supertrace_reciprocal * z - 1) == 0

print("SouriauHestenesKrein.py: finite rotor, determinant, and tripotent checks passed")
