#!/usr/bin/env python3
"""Small symbolic Jones-vector and 2×2 matrix examples.

These computations concern finite-dimensional polarization coordinates only.
They do not identify Jones matrices with all of SL(2,ℂ), a spacetime
connection, transformer attention, or fluid dynamics.
"""

from sympy import I, Matrix, exp, pi, simplify, symbols


def main() -> None:
    sigma1 = Matrix([[0, 1], [1, 0]])
    sigma2 = Matrix([[0, -I], [I, 0]])
    sigma3 = Matrix([[1, 0], [0, -1]])
    print("Finite Jones-vector and Pauli-matrix examples")
    assert simplify(sigma1 * sigma2 - sigma2 * sigma1 - 2 * I * sigma3) == Matrix.zeros(2)
    print("Pauli commutator [σ₁, σ₂] = 2 i σ₃")

    horizontal = Matrix([1, 0])
    retardance = symbols("δ", real=True)
    waveplate = Matrix([[1, 0], [0, exp(I * retardance)]])
    determinant = simplify(waveplate.det())
    print("Diagonal retarder determinant:", determinant)
    print("The matrix is unitary for real δ; it is not generally determinant one.")

    quarter_wave = waveplate.subs(retardance, pi / 2)
    print("Jones action on horizontal coordinate:", quarter_wave * horizontal)
    print("This is a matrix-coordinate example; physical conventions depend on basis and phase choice.")

    print("No Lorentz, geodesic, KMS, attention, or fluid theorem is asserted.")


if __name__ == "__main__":
    main()
