#!/usr/bin/env python3
"""Finite witness for MD 007 quantum eigenoperator interpretation.

Mirrors `InfoGeometry.Physics.MD007QuantumEigenoperatorInterpretation`.

Verified theorem-safe content only:
* computational basis outer products are matrix units;
* arbitrary 2x2 operators decompose into the E_ij basis;
* Tr(E_ij rho) reads transposed density-matrix entries;
* Pauli matrices decompose in the eigenoperator basis;
* projective and diagonal weak-measurement numerators reduce explicitly;
* depolarizing-channel action on E_ij.
"""

from __future__ import annotations

import sympy as sp


def assert_zero(expr, label: str) -> None:
    reduced = sp.expand(sp.simplify(expr))
    if reduced != 0:
        raise AssertionError(f"{label} failed:\n{reduced}")


def assert_matrix_zero(mat: sp.Matrix, label: str) -> None:
    reduced = mat.applyfunc(lambda x: sp.expand(sp.simplify(x)))
    if reduced != sp.zeros(*reduced.shape):
        raise AssertionError(f"{label} failed:\n{reduced}")


def trace2(A: sp.Matrix) -> sp.Expr:
    return sp.trace(A)


def main() -> int:
    print("=" * 72)
    print("MD 007 FINITE QUANTUM EIGENOPERATOR INTERPRETATION")
    print("=" * 72)

    ket1 = sp.Matrix([[1], [0]])
    ket2 = sp.Matrix([[0], [1]])
    E11 = sp.Matrix([[1, 0], [0, 0]])
    E12 = sp.Matrix([[0, 1], [0, 0]])
    E21 = sp.Matrix([[0, 0], [1, 0]])
    E22 = sp.Matrix([[0, 0], [0, 1]])
    I2 = sp.eye(2)
    s1 = sp.Matrix([[0, 1], [1, 0]])
    s2 = sp.Matrix([[0, -sp.I], [sp.I, 0]])
    s3 = sp.Matrix([[1, 0], [0, -1]])

    assert_matrix_zero(ket1 * ket1.T - E11, "|1><1| = E11")
    assert_matrix_zero(ket1 * ket2.T - E12, "|1><2| = E12")
    assert_matrix_zero(ket2 * ket1.T - E21, "|2><1| = E21")
    assert_matrix_zero(ket2 * ket2.T - E22, "|2><2| = E22")
    print("outer products as matrix units: OK")

    r00, r01, r10, r11 = sp.symbols("r00 r01 r10 r11")
    rho = sp.Matrix([[r00, r01], [r10, r11]])
    decomp = r00 * E11 + r01 * E12 + r10 * E21 + r11 * E22
    assert_matrix_zero(rho - decomp, "operator decomposition in E_ij basis")
    print("operator decomposition: OK")

    assert_zero(trace2(E11 * rho) - r00, "Tr(E11 rho)=rho11")
    assert_zero(trace2(E21 * rho) - r01, "Tr(E21 rho)=rho12")
    assert_zero(trace2(E12 * rho) - r10, "Tr(E12 rho)=rho21")
    assert_zero(trace2(E22 * rho) - r11, "Tr(E22 rho)=rho22")
    print("expectation/matrix-entry readouts: OK")

    assert_matrix_zero(I2 - (E11 + E22), "I = E11+E22")
    assert_matrix_zero(s1 - (E12 + E21), "sigma1 = E12+E21")
    assert_matrix_zero(s2 - (-sp.I) * (E12 - E21), "sigma2 = -i(E12-E21)")
    assert_matrix_zero(s3 - (E11 - E22), "sigma3 = E11-E22")
    print("Pauli decompositions: OK")

    assert_matrix_zero(E11 * rho * E11 - r00 * E11, "Luders numerator E11")
    assert_matrix_zero(E22 * rho * E22 - r11 * E22, "Luders numerator E22")
    print("projective measurement numerators: OK")

    a, b = sp.symbols("a b")
    K = a * E11 + b * E22
    weak_num = a**2 * r00 * E11 + a * b * r01 * E12 + b * a * r10 * E21 + b**2 * r11 * E22
    assert_matrix_zero(K * rho * K - weak_num, "diagonal weak Kraus numerator")
    print("diagonal weak-measurement numerator: OK")

    p = sp.symbols("p")

    def depol(A: sp.Matrix) -> sp.Matrix:
        return (1 - p) * A + (p / 2) * trace2(A) * I2

    assert_matrix_zero(depol(E11) - ((1 - p / 2) * E11 + (p / 2) * E22), "depolarizing E11")
    assert_matrix_zero(depol(E22) - ((p / 2) * E11 + (1 - p / 2) * E22), "depolarizing E22")
    assert_matrix_zero(depol(E12) - (1 - p) * E12, "depolarizing E12")
    assert_matrix_zero(depol(E21) - (1 - p) * E21, "depolarizing E21")
    print("depolarizing-channel finite action: OK")

    print("=" * 72)
    print("MD 007 FINITE QUANTUM EIGENOPERATOR INTERPRETATION VERIFIED")
    print("=" * 72)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
