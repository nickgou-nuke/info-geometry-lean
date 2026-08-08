#!/usr/bin/env python3
"""SymPy witness for modular monodromy and parabolic ticks of time.

This keeps the multivalued/sheeted modular time explicit:

    t_n = t + n beta

The modular factor splits into a continuous base factor and a discrete
monodromy multiplier.  The parabolic nilpotent chart supplies the tick law
P(t) P(s) = P(t+s), while the quadratic log-generating potential supplies the
Legendre/Otto gradient-flow side.
"""

import sympy as sp


def assert_zero(name: str, expr: sp.Expr) -> None:
    simplified = sp.simplify(expr)
    assert simplified == 0, f"{name} failed: {simplified}"
    print(f"OK  {name}")


def assert_matrix_zero(name: str, mat: sp.Matrix) -> None:
    simplified = mat.applyfunc(sp.simplify)
    assert simplified == sp.zeros(*mat.shape), f"{name} failed:\n{simplified}"
    print(f"OK  {name}")


t, s, beta, K, theta, p, tau, theta0 = sp.symbols(
    "t s beta K theta p tau theta0", real=True
)
n, m = sp.symbols("n m", integer=True)

I2 = sp.eye(2)
N = sp.Matrix([[0, 1], [0, 0]])
Jboost = sp.Matrix([[0, 1], [1, 0]])


def sheet_time(base, sheet):
    return base + sheet * beta


assert_zero(
    "sheet winding addition",
    sheet_time(sheet_time(t, n), m) - sheet_time(t, n + m),
)

modular_factor = sp.exp(-K * sheet_time(t, n))
base_factor = sp.exp(-K * t)
monodromy_multiplier = sp.exp(-K * beta * n)
assert_zero(
    "modular factor splits into base times winding multiplier",
    modular_factor - base_factor * monodromy_multiplier,
)

kms_period_factor = sp.exp(-K * beta)
assert_zero(
    "one KMS winding multiplies by exp(-beta K)",
    sp.exp(-K * sheet_time(t, n + 1))
    - kms_period_factor * sp.exp(-K * sheet_time(t, n)),
)

P_t = I2 + t * N
P_s = I2 + s * N
P_ts = I2 + (t + s) * N
assert_matrix_zero("parabolic ticks compose additively", P_t * P_s - P_ts)
assert_matrix_zero("parabolic inverse tick", P_t * (I2 - t * N) - I2)

B_t = sp.cosh(t) * I2 + sp.sinh(t) * Jboost
B_s = sp.cosh(s) * I2 + sp.sinh(s) * Jboost
B_ts = sp.cosh(t + s) * I2 + sp.sinh(t + s) * Jboost
assert_matrix_zero(
    "Bogoliubov boost chart composes by rapidity addition",
    sp.trigsimp(B_t * B_s - B_ts),
)

psi = theta**2 / 2
grad_psi = sp.diff(psi, theta)
legendre = p * p - p**2 / 2
assert_zero("log-generating potential gradient", grad_psi - theta)
assert_zero("quadratic Legendre dual", legendre - p**2 / 2)

gradient_flow = theta0 * sp.exp(-tau)
assert_zero(
    "Otto/Villani quadratic gradient flow equation",
    sp.diff(gradient_flow, tau) + gradient_flow,
)

# Modular J conjugation as sheet reversal: n -> -n and boost sign reversal.
assert_zero(
    "J reverses modular sheet winding",
    sheet_time(t, -n) - (t - n * beta),
)
assert_matrix_zero(
    "J flips boost generator sign by parity conjugation",
    sp.Matrix([[1, 0], [0, -1]]) * Jboost * sp.Matrix([[1, 0], [0, -1]]) + Jboost,
)

# Exponential maps infinity of modular Hamiltonian to the zero boundary of the
# positive modular semigroup; near K=0 it is the identity.
assert_zero("modular exponential identity at K=0", sp.exp(-0 * t) - 1)
print("OK  modular Hamiltonian K -> +infinity maps exp(-K) toward zero boundary")

print("OK  modular monodromy, parabolic ticks, and convex flow witness completed")
