#!/usr/bin/env python3
"""SymPy witnesses for GellMannParafermionSolder.lean.

Checks the explicit soldering idea:
  * a 3+1 spinor has three color lanes and one singlet lane;
  * Gell-Mann matrices act on the triplet and give zero infinitesimal singlet;
  * the action represents commutators;
  * selected and all listed Gell-Mann commutators match the repository table.
"""

import sympy as sp

I = sp.I

# Gell-Mann generators in the same normalization as proofs/GellMannSU3.lean.
gl1 = sp.Matrix([[0, 1, 0], [1, 0, 0], [0, 0, 0]])
gl2 = sp.Matrix([[0, -I, 0], [I, 0, 0], [0, 0, 0]])
gl3 = sp.Matrix([[1, 0, 0], [0, -1, 0], [0, 0, 0]])
gl4 = sp.Matrix([[0, 0, 1], [0, 0, 0], [1, 0, 0]])
gl5 = sp.Matrix([[0, 0, -I], [0, 0, 0], [I, 0, 0]])
gl6 = sp.Matrix([[0, 0, 0], [0, 0, 1], [0, 1, 0]])
gl7 = sp.Matrix([[0, 0, 0], [0, 0, -I], [0, I, 0]])
gl8 = sp.Matrix([[1, 0, 0], [0, 1, 0], [0, 0, -2]])

p0, p1, p2, ell = sp.symbols("p0 p1 p2 ell")
color = sp.Matrix([p0, p1, p2])


def act(A, c=color):
    """Infinitesimal soldered color action: A on triplet, zero on singlet."""
    return A * c, 0


def assert_zero(expr, name):
    if isinstance(expr, sp.MatrixBase):
        z = sp.simplify(expr)
        assert z == sp.zeros(*expr.shape), f"{name} failed:\n{z}"
    else:
        z = sp.simplify(expr)
        assert z == 0, f"{name} failed: {z}"


def assert_comm(A, B, RHS, name):
    # Matrix commutator table.
    assert_zero(A * B - B * A - RHS, name + " matrix")
    # Soldered action commutator on triplet.
    lhs_color, lhs_singlet = act(RHS)
    rhs_color = A * (B * color) - B * (A * color)
    assert_zero(lhs_color - rhs_color, name + " action")
    assert_zero(lhs_singlet, name + " singlet neutral")

commutators = [
    (gl1, gl2, 2 * I * gl3, "[gl1,gl2]"),
    (gl1, gl3, -2 * I * gl2, "[gl1,gl3]"),
    (gl2, gl3, 2 * I * gl1, "[gl2,gl3]"),
    (gl1, gl6, I * gl5, "[gl1,gl6]"),
    (gl1, gl7, -I * gl4, "[gl1,gl7]"),
    (gl2, gl6, -I * gl4, "[gl2,gl6]"),
    (gl2, gl7, -I * gl5, "[gl2,gl7]"),
    (gl3, gl4, I * gl5, "[gl3,gl4]"),
    (gl3, gl5, -I * gl4, "[gl3,gl5]"),
    (gl4, gl6, I * gl2, "[gl4,gl6]"),
    (gl4, gl7, I * gl1, "[gl4,gl7]"),
    (gl5, gl6, -I * gl1, "[gl5,gl6]"),
    (gl5, gl7, I * gl2, "[gl5,gl7]"),
    (gl3, gl8, sp.zeros(3), "[gl3,gl8]"),
    (gl4, gl8, -3 * I * gl5, "[gl4,gl8]"),
    (gl5, gl8, 3 * I * gl4, "[gl5,gl8]"),
]

for A, B, RHS, name in commutators:
    assert_comm(A, B, RHS, name)

# Chemical-potential/braid phase witness.
beta, dmu, Q, theta, E, mu = sp.symbols("beta dmu Q theta E mu")
log_clock = theta - beta * (E - mu * Q)
shifted = theta - beta * (E - (mu + dmu) * Q)
assert_zero(sp.exp(shifted) - sp.exp(beta * dmu * Q) * sp.exp(log_clock), "phase shift")

print("gellmann_parafermion_solder.py: all witnesses passed")
