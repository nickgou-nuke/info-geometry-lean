from __future__ import annotations

import sympy as sp

I4 = sp.eye(4)
I = sp.I

# Dirac-Pauli gamma matrices from the committed Lean owner surface.
gamma1 = sp.Matrix([
    [0, 0, 0, 1],
    [0, 0, 1, 0],
    [0, -1, 0, 0],
    [-1, 0, 0, 0],
])

gamma2 = sp.Matrix([
    [0, 0, 0, -I],
    [0, 0, I, 0],
    [0, I, 0, 0],
    [-I, 0, 0, 0],
])

gamma3 = sp.Matrix([
    [0, 0, 1, 0],
    [0, 0, 0, -1],
    [-1, 0, 0, 0],
    [0, 1, 0, 0],
])

qi = gamma1 * gamma2
qj = gamma2 * gamma3
qk = gamma3 * gamma1

assert sp.simplify(qi * qi + I4) == sp.zeros(4)
assert sp.simplify(qj * qj + I4) == sp.zeros(4)
assert sp.simplify(qk * qk + I4) == sp.zeros(4)
assert sp.simplify(qi * qj - qk) == sp.zeros(4)
assert sp.simplify(qj * qk - qi) == sp.zeros(4)
assert sp.simplify(qk * qi - qj) == sp.zeros(4)
assert sp.simplify(qi * qj * qk + I4) == sp.zeros(4)


def quaternion_field(a: sp.Expr, b: sp.Expr, c: sp.Expr, d: sp.Expr) -> sp.Matrix:
    return a * I4 + b * qi + c * qj + d * qk


def quaternion_conj(a: sp.Expr, b: sp.Expr, c: sp.Expr, d: sp.Expr) -> sp.Matrix:
    return a * I4 - b * qi - c * qj - d * qk


a, b, c, d = sp.symbols("a b c d", real=True)
field = quaternion_field(a, b, c, d)
field_conj = quaternion_conj(a, b, c, d)
expected_norm = (a**2 + b**2 + c**2 + d**2) * I4
assert sp.simplify(field_conj * field - expected_norm) == sp.zeros(4)

z = sp.symbols("z")
x, y = sp.symbols("x y", real=True)
complex_sample = x + I * y
anti_hermitian_readout = (I / 2) * (complex_sample - sp.conjugate(complex_sample))
assert sp.simplify(anti_hermitian_readout + y) == 0
assert sp.simplify(sp.im(anti_hermitian_readout)) == 0

eta = sp.diag(1, -1, -1, -1)
e = sp.Matrix([
    [1, 2, 0, 1],
    [0, 1, 3, 0],
    [2, 0, 1, 4],
    [1, 1, 0, 2],
])
g = e.T * eta * e
assert g == g.T

kappa = sp.Rational(5, 7)
C012 = {
    (0, 1, 2): sp.Integer(3),
    (0, 2, 1): sp.Integer(-4),
}

def C(rho: int, mu: int, nu: int) -> sp.Expr:
    return C012.get((rho, mu, nu), sp.Integer(0))


def torsion_from_commutator(rho: int, mu: int, nu: int) -> sp.Expr:
    return sp.simplify(kappa * (C(rho, mu, nu) - C(rho, nu, mu)))

assert sp.simplify(torsion_from_commutator(0, 1, 2) + torsion_from_commutator(0, 2, 1)) == 0

print("Quaternionic emergent-gravity finite foundation checks passed.")
print(f"qi^2 =\n{sp.simplify(qi * qi)}")
print(f"qi*qj - qk =\n{sp.simplify(qi * qj - qk)}")
print(f"field_conj * field diagonal scalar = {a**2 + b**2 + c**2 + d**2}")
print(f"anti-Hermitian readout = {sp.simplify(anti_hermitian_readout)}")
print(f"metric symmetric = {g == g.T}")
print(f"torsion antisymmetry sample = {sp.simplify(torsion_from_commutator(0, 1, 2) + torsion_from_commutator(0, 2, 1))}")
print("Honest scope: finite Clifford/quaternion identities and algebraic readouts only; no full analytic Einstein-Cartan bootstrap claimed.")
