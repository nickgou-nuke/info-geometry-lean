#!/usr/bin/env python3
"""
SymPy witness for the Hestenes / Krein / Klein operator-algebra readout.

This script checks the finite matrix identities that mirror the Lean operator
theorems in `InfoGeometry.Quantum.RealKCategory`:

- grading involution `Gamma` with `Gamma^2 = I`
- fixed-point / odd-part decomposition by conjugation
- rotor composition `R(theta1) R(theta2) = R(theta1 + theta2)`
- nilpotent binomial collapse when `N^2 = 0`
- monodromy power reduction `M^n = R(n theta) (I + n c N)`

The point is not to prove the universal Lean theorem.
The point is to witness the finite Hestenes/Krein/Klein operator pattern
explicitly in matrices.
"""

import sys
from pathlib import Path
import sympy as sp
from sympy import Matrix, eye, zeros

_REPO_ROOT = Path(__file__).resolve().parents[2]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

from tools.sympy.common import comm


def is_zero(m: Matrix) -> bool:
    return m.equals(zeros(*m.shape))


def eq(a: Matrix, b: Matrix) -> bool:
    return is_zero(sp.simplify(a - b))


def rotor(k: Matrix, theta):
    return sp.cos(theta) * eye(k.rows) + sp.sin(theta) * k


def monodromy(k: Matrix, n: Matrix, theta, c):
    return rotor(k, theta) * (eye(k.rows) + c * n)


def fixed_point_part(gamma: Matrix, a: Matrix) -> Matrix:
    return sp.simplify((a + gamma * a * gamma) / 2)


def odd_part(gamma: Matrix, a: Matrix) -> Matrix:
    return sp.simplify((a - gamma * a * gamma) / 2)


I4 = eye(4)

# A split grading involution: fixed-point algebra = block diagonal operators.
Gamma = Matrix.diag(1, 1, -1, -1)

# A complex-structure / clock operator on the real carrier.
K = Matrix([
    [0, -1, 0, 0],
    [1,  0, 0, 0],
    [0,  0, 0, -1],
    [0,  0, 1,  0],
])

# A nilpotent shear commuting with K.
N = Matrix([
    [0, 0, 1, 0],
    [0, 0, 0, 1],
    [0, 0, 0, 0],
    [0, 0, 0, 0],
])

theta, theta1, theta2, c = sp.symbols("theta theta1 theta2 c", real=True)
n = sp.symbols("n", integer=True, nonnegative=True)

# A generic operator used to witness the conjugation decomposition.
a00, a01, a02, a03, a10, a11, a12, a13, a20, a21, a22, a23, a30, a31, a32, a33 = sp.symbols(
    "a00 a01 a02 a03 a10 a11 a12 a13 a20 a21 a22 a23 a30 a31 a32 a33"
)
A = Matrix([
    [a00, a01, a02, a03],
    [a10, a11, a12, a13],
    [a20, a21, a22, a23],
    [a30, a31, a32, a33],
])

R1 = rotor(K, theta1)
R2 = rotor(K, theta2)
R = rotor(K, theta)
M = monodromy(K, N, theta, c)


checks = {
    # grading involution
    "Gamma^2 = I": eq(Gamma * Gamma, I4),
    "fixed-point projection is invariant":
        eq(Gamma * fixed_point_part(Gamma, A) * Gamma, fixed_point_part(Gamma, A)),
    "odd-part projection flips sign":
        eq(Gamma * odd_part(Gamma, A) * Gamma, -odd_part(Gamma, A)),
    "A = even + odd": eq(A, fixed_point_part(Gamma, A) + odd_part(Gamma, A)),

    # rotor / complex structure
    "K^2 = -I": eq(K * K, -I4),
    "rotor composition": eq(R1 * R2, rotor(K, theta1 + theta2)),
    "rotor commutes with K": eq(comm(R, K), zeros(4)),

    # nilpotent shear
    "N^2 = 0": eq(N * N, zeros(4)),
    "N commutes with K": eq(comm(N, K), zeros(4)),
    "R commutes with N": eq(comm(R, N), zeros(4)),
    "Gamma commutes with R": eq(comm(Gamma, R), zeros(4)),
    "Gamma anti-commutes with N": eq(Gamma * N * Gamma, -N),
}


def monodromy_power_formula(k: int, theta_value, c_value):
    return rotor(K, k * theta_value) * (eye(4) + (k * c_value) * N)


print("Hestenes / Krein / Klein SymPy witness")
print("--------------------------------------")
for key in [
    "Gamma^2 = I",
    "fixed-point projection is invariant",
    "odd-part projection flips sign",
    "A = even + odd",
]:
    print(f"  {key}: {checks[key]}")

print("\nRotor / complex-structure readout:")
for key in ["K^2 = -I", "rotor composition", "rotor commutes with K"]:
    print(f"  {key}: {checks[key]}")

print("\nNilpotent / shear readout:")
for key in ["N^2 = 0", "N commutes with K", "R commutes with N", "Gamma commutes with R", "Gamma anti-commutes with N"]:
    print(f"  {key}: {checks[key]}")

print("\nMonodromy power witness:")
pow_checks = []
theta0 = sp.pi / 3
c0 = sp.Integer(2)
M0 = monodromy(K, N, theta0, c0)
for k in range(0, 7):
    lhs = eye(4)
    for _ in range(k):
        lhs = sp.simplify(lhs * M0)
    rhs = sp.simplify(monodromy_power_formula(k, theta0, c0))
    ok = eq(lhs, rhs)
    pow_checks.append(ok)
    print(f"  n = {k}: {ok}")

print("\nInterpretation:")
print("  Gamma-fixed operators form the even subalgebra / fixed-point algebra.")
print("  The odd part is the Gamma-anti-invariant sector.")
print("  Rotor powers add angles.")
print("  Nilpotent corrections grow linearly because N^2 = 0.")
print("  This is the finite Hestenes/Krein/Klein witness for the Lean operator lane.")
print("OVERALL:", all(checks.values()) and all(pow_checks))
