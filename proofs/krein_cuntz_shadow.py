#!/usr/bin/env python3
"""
Krein--Cuntz finite shadow: exact SymPy witness.

This mirrors proofs/KreinCuntzShadow.lean.  It verifies the finite chiral
matrix-unit/CAR shadow, the indefinite Krein metric eta=diag(1,-1), the Krein
adjoint A^x = eta A^dag eta, and exact matrix-element reconstruction.

It is not a C*-O_2 completion, Tomita--Takesaki theorem, KMS construction, or
Lorentz/Pin(5,5) proof.  Those are deferred_interface in Lean.
"""

import sys
from pathlib import Path
import sympy as sp

_REPO_ROOT = Path(__file__).resolve().parents[1]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

from tools.sympy.common import assert_matrix_eq

I = sp.I

eta = sp.Matrix([[1, 0], [0, -1]])
Id = sp.eye(2)
Z = sp.zeros(2)

Nplus = sp.Matrix([[1, 0], [0, 0]])
Nminus = sp.Matrix([[0, 0], [0, 1]])
Splus = sp.Matrix([[0, 1], [0, 0]])
Sminus = sp.Matrix([[0, 0], [1, 0]])
sigma_x = sp.Matrix([[0, 1], [1, 0]])


def dagger(A: sp.Matrix) -> sp.Matrix:
    return A.conjugate().T


def krein_adjoint(A: sp.Matrix) -> sp.Matrix:
    return eta * dagger(A) * eta


def act(A: sp.Matrix, v: sp.Matrix) -> sp.Matrix:
    return A * v


def matrix_element(bra: sp.Matrix, A: sp.Matrix, ket: sp.Matrix) -> sp.Expr:
    return (dagger(bra) * A * ket)[0]


def transition_probability(bra: sp.Matrix, A: sp.Matrix, ket: sp.Matrix) -> sp.Expr:
    amp = matrix_element(bra, A, ket)
    return sp.simplify(sp.conjugate(amp) * amp)


def swap_state(v: sp.Matrix) -> sp.Matrix:
    return sigma_x * v


def swap_operator(A: sp.Matrix) -> sp.Matrix:
    return sigma_x * A * sigma_x


def main() -> None:
    # Chiral matrix-unit/CAR shadow.
    assert_matrix_eq(Splus * Splus, Z, "Splus nilpotent")
    assert_matrix_eq(Sminus * Sminus, Z, "Sminus nilpotent")
    assert_matrix_eq(Splus * Sminus, Nplus, "Splus Sminus = Nplus")
    assert_matrix_eq(Sminus * Splus, Nminus, "Sminus Splus = Nminus")
    assert_matrix_eq(Splus * Sminus + Sminus * Splus, Id, "completeness")

    # Finite honesty boundary: partial isometry, not literal finite O_2 isometry.
    assert_matrix_eq(dagger(Splus) * Splus, Nminus, "Splus^dag Splus = Nminus")
    assert_matrix_eq(dagger(Sminus) * Sminus, Nplus, "Sminus^dag Sminus = Nplus")
    assert dagger(Splus) * Splus != Id

    # Krein metric and adjoint.
    assert_matrix_eq(eta * eta, Id, "eta^2=I")
    assert_matrix_eq(dagger(eta), eta, "eta self-adjoint")
    assert_matrix_eq(krein_adjoint(Splus), -Sminus, "Krein adjoint Splus")
    assert_matrix_eq(krein_adjoint(Sminus), -Splus, "Krein adjoint Sminus")
    assert_matrix_eq(krein_adjoint(Nplus), Nplus, "Krein adjoint Nplus")
    assert_matrix_eq(krein_adjoint(Nminus), Nminus, "Krein adjoint Nminus")

    # Matrix elements reconstruct entries.
    e0 = sp.Matrix([1, 0])
    e1 = sp.Matrix([0, 1])
    basis = [e0, e1]
    a00, a01, a10, a11 = sp.symbols("a00 a01 a10 a11")
    A = sp.Matrix([[a00, a01], [a10, a11]])
    table = sp.Matrix([[matrix_element(basis[i], A, basis[j]) for j in range(2)] for i in range(2)])
    assert_matrix_eq(table, A, "matrix element table reconstructs A")

    # Linearity in operator.
    b00, b01, b10, b11, c = sp.symbols("b00 b01 b10 b11 c")
    B = sp.Matrix([[b00, b01], [b10, b11]])
    bra = sp.Matrix([sp.symbols("u0"), sp.symbols("u1")])
    ket = sp.Matrix([sp.symbols("v0"), sp.symbols("v1")])
    assert sp.simplify(matrix_element(bra, A + B, ket) - matrix_element(bra, A, ket) - matrix_element(bra, B, ket)) == 0
    assert sp.simplify(matrix_element(bra, c * A, ket) - c * matrix_element(bra, A, ket)) == 0

    # Exact covariance under swap basis change.
    assert sp.simplify(
        matrix_element(swap_state(bra), swap_operator(A), swap_state(ket))
        - matrix_element(bra, A, ket)
    ) == 0
    assert sp.simplify(
        transition_probability(swap_state(bra), swap_operator(A), swap_state(ket))
        - transition_probability(bra, A, ket)
    ) == 0

    print("krein_cuntz_shadow.py: exact SymPy witnesses passed")
    print("  finite chiral Cuntz/CAR shadow: closed")
    print("  eta^2=I and Krein adjoint action: closed")
    print("  matrix-element reconstruction/covariance: closed")
    print("  full C*-O2/Tomita/KMS/Lorentz completion: deferred_interface")


if __name__ == "__main__":
    main()
