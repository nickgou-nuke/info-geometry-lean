#!/usr/bin/env python3
"""Finite regularization, spectral squashing, and Cayley-coordinate checks.

This is the executable witness for the finite-stage pipeline:

    T -> T - I -> tanh(I - T^{-1})
    T -> (T - iI)(T + iI)^{-1}

The point is deliberately modest: before any colimit is taken, the concrete
matrix coordinates are bounded or unitary, so the infinite-stage object can be
tracked through bounded C*-algebra coordinates instead of raw unbounded spectra.
"""

from __future__ import annotations

import sympy as sp


def diagonal_function(matrix: sp.Matrix, function) -> sp.Matrix:
    """Apply a scalar function to a diagonal matrix."""
    rows, cols = matrix.shape
    if rows != cols:
        raise ValueError("expected a square matrix")
    for row in range(rows):
        for col in range(cols):
            if row != col and sp.simplify(matrix[row, col]) != 0:
                raise ValueError("expected a diagonal matrix")
    return sp.diag(*[function(matrix[index, index]) for index in range(rows)])


def krein_tomita_adjoint(x: sp.Matrix, eta: sp.Matrix, modular_j: sp.Matrix) -> sp.Matrix:
    """Finite matrix model of X^star = J eta X* eta J."""
    return modular_j * eta * x.H * eta * modular_j


def main() -> None:
    print("=== finite regularization / squashing / Cayley pipeline ===")

    lam = sp.symbols("lam", positive=True, real=True)
    eye = sp.eye(2)
    imaginary = sp.I

    # A finite-stage positive self-adjoint operator with growing eigenvalues.
    operator = sp.diag(lam, 2 * lam)
    regularized = operator - eye
    relative = eye - operator.inv()
    squashed = diagonal_function(relative, sp.tanh)
    cayley = (operator - imaginary * eye) * (operator + imaginary * eye).inv()

    print("\n1. raw and regularized coordinates")
    print(f"T = {operator}")
    print(f"T - I = {regularized}")

    print("\n2. tanh squashing")
    print(f"tanh(I - T^-1) = {squashed}")
    squash_limit = squashed.applyfunc(lambda entry: sp.limit(entry, lam, sp.oo))
    print(f"limit as lambda -> oo = {squash_limit}")
    assert squash_limit == sp.diag(sp.tanh(1), sp.tanh(1))
    assert all(sp.simplify(entry - sp.tanh(1)) == 0 for entry in squash_limit.diagonal())

    print("\n3. Cayley transform")
    print(f"C(T) = {sp.simplify(cayley)}")
    unitary_residual = sp.simplify(cayley.H * cayley - eye)
    print(f"C(T)* C(T) - I = {unitary_residual}")
    assert unitary_residual == sp.zeros(2)
    cayley_limit = cayley.applyfunc(lambda entry: sp.limit(entry, lam, sp.oo))
    print(f"limit as lambda -> oo = {cayley_limit}")
    assert cayley_limit == eye

    print("\n4. unified Dirac-Krein-Tomita adjoint")
    eta = sp.diag(1, -1)
    modular_j = sp.diag(1, -1)
    assert eta.H == eta and eta * eta == eye
    assert modular_j.H == modular_j and modular_j * modular_j == eye
    assert eta * modular_j == modular_j * eta

    a, b, c, d = sp.symbols("a b c d", complex=True)
    x = sp.Matrix([[a, b], [c, d]])
    x_star = krein_tomita_adjoint(x, eta, modular_j)
    involution_residual = sp.simplify(krein_tomita_adjoint(x_star, eta, modular_j) - x)
    print(f"(X^star)^star - X = {involution_residual}")
    assert involution_residual == sp.zeros(2)

    y0, y1, y2, y3 = sp.symbols("y0 y1 y2 y3", complex=True)
    y = sp.Matrix([[y0, y1], [y2, y3]])
    anti_mul_residual = sp.simplify(
        krein_tomita_adjoint(x * y, eta, modular_j)
        - krein_tomita_adjoint(y, eta, modular_j) * krein_tomita_adjoint(x, eta, modular_j)
    )
    print(f"(XY)^star - Y^star X^star = {anti_mul_residual}")
    assert anti_mul_residual == sp.zeros(2)

    print("\nregularization_cayley_pipeline.py: all checks passed")


if __name__ == "__main__":
    main()
