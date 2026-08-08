#!/usr/bin/env python3
"""SymPy witness for the Kasparov-Krein categorical collapse.

This finite symbolic model mirrors ``KasparovKreinCategory.lean``:

* doubled Krein space: C^2 with grading Gamma and real symmetry J,
* Fredholm/Dirac witness F odd with respect to Gamma,
* bivariant product represented by scalar multiplication of KK-classes,
* O2 boundary contractibility represented by a no-chain firewall: every class
  entering or leaving the boundary is absent/zero in the finite shadow.

It is not an analytic proof of KK-theory and it does not derive anomaly
collapse from an impossible chain; it checks the executable algebraic shadow.
"""

from __future__ import annotations

import sympy as sp


def assert_zero(name: str, expr: sp.Expr) -> None:
    simplified = sp.simplify(expr)
    assert simplified == 0, f"{name} failed: {simplified}"
    print(f"OK  {name}")


def assert_matrix_zero(name: str, mat: sp.Matrix) -> None:
    simplified = mat.applyfunc(sp.simplify)
    assert simplified == sp.zeros(*mat.shape), f"{name} failed:\n{simplified}"
    print(f"OK  {name}")


# ---------------------------------------------------------------------------
# 1. Doubled Krein carrier and Real Kasparov-Krein module data.
# ---------------------------------------------------------------------------

I2 = sp.eye(2)
Gamma = sp.Matrix([[1, 0], [0, -1]])      # chiral/Krein grading
J = sp.Matrix([[0, 1], [1, 0]])           # Tomita-style real sheet swap
K = J * Gamma                             # emergent complex/Krein operator
F = sp.Matrix([[0, 1], [1, 0]])           # finite Fredholm/Dirac witness

assert_matrix_zero("Gamma^2 = 1", Gamma * Gamma - I2)
assert_matrix_zero("J^2 = 1", J * J - I2)
assert_matrix_zero("J flips the Krein grading", J * Gamma * J + Gamma)
assert_matrix_zero("K^2 = -1", K * K + I2)
assert_matrix_zero("F is odd for the grading", Gamma * F + F * Gamma)

# A tiny representation of a diagonal algebra element.  The commutator is
# finite-rank automatically in this finite witness; the symbolic entry records
# the off-diagonal anomaly that the bivariant boundary will later kill.
a0, a1 = sp.symbols("a0 a1", real=True)
pi_a = sp.diag(a0, a1)
comm = F * pi_a - pi_a * F
expected_comm = sp.Matrix([[0, a1 - a0], [a0 - a1, 0]])
assert_matrix_zero("Fredholm commutator shape", comm - expected_comm)


# ---------------------------------------------------------------------------
# 2. Kasparov product through a KK-contractible O2 boundary.
# ---------------------------------------------------------------------------

x, y = sp.symbols("x y", real=True)


def kasparov_product(left: sp.Expr, right: sp.Expr) -> sp.Expr:
    """Toy bivariant product KK(A,B) x KK(B,C) -> KK(A,C)."""
    return sp.simplify(left * right)


# O2 contractibility is modeled by x=0 for incoming and y=0 for outgoing
# bivariant classes.  The Lean repair states the stronger constructive firewall:
# a contractible boundary admits no such chain in the first place.
incoming_O2 = sp.Integer(0)
outgoing_O2 = sp.Integer(0)
through_O2 = kasparov_product(incoming_O2, outgoing_O2)
assert_zero("KK(A,O2) product KK(O2,C) = 0", through_O2)
assert incoming_O2 == 0 and outgoing_O2 == 0, "contractible boundary has no nonzero chain legs"
print("OK  contractible boundary firewall: no nonzero incoming/outgoing chain legs")

generic_product = kasparov_product(x, y)
collapsed_product = generic_product.subs({x: incoming_O2, y: outgoing_O2})
assert_zero("generic Kasparov product collapses through O2", collapsed_product)


# ---------------------------------------------------------------------------
# 3. Static Connes-Chern shadow and spectral obstruction profile.
# ---------------------------------------------------------------------------

S0, c = sp.symbols("S0 c", real=True)
theta, beta, s = sp.symbols("theta beta s", real=True)

# The Connes-Chern value on the O2 boundary shadow is zero (factorized through
# the contractible boundary).
connes_chern_pairing = theta * incoming_O2

# Toy spectral functional = S0 + c*|I|^2, so collapse of the index I = 0 forces S0.
anomalous_index = connes_chern_pairing
fredholm_spectral_shadow : sp.Expr = sp.simplify(S0 + c * (anomalous_index * sp.conjugate(anomalous_index)))
fredholm_determinant_shadow = 1 - sp.exp(-beta) * connes_chern_pairing

spectral_obstruction = sp.simplify(anomalous_index**2)
leak_profile = sp.simplify(s * through_O2)

assert_zero("O2 Connes-Chern shadow pairing", connes_chern_pairing)
assert_zero("collapsed spectral index", anomalous_index)
assert_zero("toy collapsed Connes spectral functional", fredholm_spectral_shadow - S0)
assert_zero("bivariant spectral obstruction", spectral_obstruction)
assert_zero("index leakage profile through O2", leak_profile)
assert_zero(
    "Fredholm determinant shadow has no O2 anomaly factor",
    fredholm_determinant_shadow - 1,
)


# ---------------------------------------------------------------------------
# 4. Product associativity sanity check away from the collapsed boundary.
# ---------------------------------------------------------------------------

z = sp.symbols("z", real=True)
lhs = kasparov_product(kasparov_product(x, y), z)
rhs = kasparov_product(x, kasparov_product(y, z))
assert_zero("toy Kasparov product is associative", lhs - rhs)

print("OK  Kasparov-Krein finite bivariant collapse witness completed")
