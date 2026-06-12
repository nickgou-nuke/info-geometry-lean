#!/usr/bin/env python3
"""Repaired Section 30 finite Pauli/Bloch/Minkowski matrix algebra.

Mirrors `InfoGeometry.Physics.Section30UnifiedMatrixFramework`.

Checks:
- Pauli square and multiplication identities;
- corrected quaternion sign: (iσ1)(iσ2) = -iσ3;
- determinant/Minkowski identity for tI+xσ1+yσ2+zσ3;
- Bloch trace and determinant formulas.

No gravity-from-entanglement, Einstein-equation derivation, Riemann-sphere
smooth equivalence, or spacetime-emergence theorem is asserted.
"""

import sympy as sp


def main() -> None:
    I = sp.I
    sigma1 = sp.Matrix([[0, 1], [1, 0]])
    sigma2 = sp.Matrix([[0, -I], [I, 0]])
    sigma3 = sp.Matrix([[1, 0], [0, -1]])
    eye = sp.eye(2)

    pauli_squares = [sigma1**2 == eye, sigma2**2 == eye, sigma3**2 == eye]
    pauli_products = [
        sigma1 * sigma2 == I * sigma3,
        sigma2 * sigma3 == I * sigma1,
        sigma3 * sigma1 == I * sigma2,
    ]

    quat_i = I * sigma1
    quat_j = I * sigma2
    quat_k = -I * sigma3
    quat_checks = [
        quat_i**2 == -eye,
        quat_j**2 == -eye,
        quat_k**2 == -eye,
        quat_i * quat_j == quat_k,
    ]

    t, x, y, z = sp.symbols("t x y z", real=True)
    M = t * eye + x * sigma1 + y * sigma2 + z * sigma3
    det_formula = sp.simplify(M.det() - (t**2 - x**2 - y**2 - z**2)) == 0
    minkowski_formula = sp.simplify(-M.det() - (-t**2 + x**2 + y**2 + z**2)) == 0

    nx, ny, nz = sp.symbols("nx ny nz", real=True)
    rho = sp.Rational(1, 2) * (eye + nx * sigma1 + ny * sigma2 + nz * sigma3)
    bloch_trace = sp.simplify(sp.trace(rho) - 1) == 0
    bloch_det = sp.simplify(rho.det() - (1 - nx**2 - ny**2 - nz**2) / 4) == 0
    pure_det_zero = sp.simplify(rho.det().subs(nz**2, 1 - nx**2 - ny**2)) == 0

    print("=== Repaired Section 30 finite matrix framework ===")
    print(f"Pauli squares: {pauli_squares}")
    print(f"Pauli products: {pauli_products}")
    print(f"Corrected quaternion checks: {quat_checks}")
    print(f"det(tI+xσ1+yσ2+zσ3) = t²-x²-y²-z²: {det_formula}")
    print(f"-det equals Minkowski (-,+,+,+) form: {minkowski_formula}")
    print(f"Bloch trace = 1: {bloch_trace}")
    print(f"Bloch determinant formula: {bloch_det}")
    print(f"Unit Bloch vector implies determinant zero: {pure_det_zero}")

    checks = pauli_squares + pauli_products + quat_checks + [
        det_formula,
        minkowski_formula,
        bloch_trace,
        bloch_det,
        pure_det_zero,
    ]
    if all(checks):
        print("[SUCCESS] repaired finite Section 30 matrix identities verified.")


if __name__ == "__main__":
    main()
