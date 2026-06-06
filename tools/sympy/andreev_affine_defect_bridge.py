#!/usr/bin/env python3
"""
SymPy bridge test: affine cocycle defect on Andreev (particle-hole) phase flow.

This witness checks that the Weyl/Klein torus noncommutation defect modifies the
Andreev operator by an explicit phase-conjugation cocycle, i.e. a crossed-action
correction on the 2×2 particle-hole channel.
"""

import sympy as sp
from sympy import Matrix, zeros

I = sp.I


def is_zero(m: Matrix) -> bool:
    return m.equals(zeros(*m.shape))


def eq(a: Matrix, b: Matrix) -> bool:
    return is_zero(sp.simplify(a - b))


def andreev(theta: sp.Expr) -> Matrix:
    """Particle-hole / BdG involutive atom A(θ) = [[0,-e^{iθ}], [e^{-iθ}, 0]]."""
    return Matrix([[0, -sp.exp(I * theta)], [sp.exp(-I * theta), 0]])


def phase_rot(theta: sp.Expr) -> Matrix:
    """Phase-rotation implementing conjugacy on Andreev: R(θ) A(φ) R(θ)⁻¹ = A(φ+θ)."""
    return Matrix([[sp.exp(I * theta / 2), 0], [0, sp.exp(-I * theta / 2)]])


def main() -> int:
    t1, t2 = sp.symbols("theta1 theta2", real=True)

    checks = {}

    # Klein (A) and Weyl (W) actions on torus coordinates
    W = Matrix([[-t1 + t2, t2]])
    K = Matrix([t1 + sp.pi, -t2])

    KW = Matrix([W[0] + sp.pi, -W[1]])
    WK = Matrix([-K[0] + K[1], K[1]])

    defect = sp.simplify(KW[0] - WK[0])
    # The defect itself is explicit and depends on θ₂ (plus a 2π winding contribution).
    checks["defect vector = (2*θ₂ + 2π, 0)"] = (
        sp.simplify(KW - WK) == Matrix([[2 * t2 + 2 * sp.pi], [0]])
    )
    checks["defect first component"] = (
        sp.simplify(defect - (2 * t2 + 2 * sp.pi)) == 0
    )

    # phase choices inherited by the two compositions
    phi_WK = WK[0]
    phi_KW = KW[0]

    A_WK = andreev(phi_WK)
    A_KW = andreev(phi_KW)

    # Structural Andreev identities
    checks["A(θ)^2 = -I"] = eq(andreev(t1) * andreev(t1), -sp.eye(2))
    checks["A(0)^4 = I"] = eq(andreev(0) ** 4, sp.eye(2))
    # Affine cocycle on Andreev induced by KW/WK mismatch
    checks["A_KW = R(defect) * A_WK * R(defect)^{-1}"] = eq(
        A_KW, phase_rot(defect) * A_WK * phase_rot(-defect)
    )

    checks["A_KW conjugacy defect formula"] = eq(
        A_KW,
        phase_rot(defect) * A_WK * phase_rot(-defect),
    )

    # Vector-level witness for a generic BdG spinor
    e, h = sp.symbols("e h", complex=True)
    psi = Matrix([e, h])

    checks["Andreev action vector on (e,h)"] = (
        andreev(t1) * psi == Matrix([-sp.exp(I * t1) * h, sp.exp(-I * t1) * e])
    )

    # Compare two orderings with same bare input; shifted order is absorbed by phase twist
    checks["phase-twisted KW output"] = eq(
        phase_rot(defect) * (A_WK * psi),
        A_KW * phase_rot(defect) * psi,
    )

    print("Andreev + affine defect bridge")
    print("============================")
    for k, v in checks.items():
        print(f"{k}: {v}")

    overall = all(v for v in checks.values())
    print("OVERALL:", overall)
    if not overall:
        failed = [k for k, v in checks.items() if v is not True]
        print("FAILED:", failed)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
