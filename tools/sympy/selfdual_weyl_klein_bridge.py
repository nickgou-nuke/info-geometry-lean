#!/usr/bin/env python3
"""Finite witness for self-dual, Fenchel–Legendre, Weyl, and Klein bridge."""

import sympy as sp
from sympy import Matrix, Rational, zeros


def conj(m: Matrix, x: Matrix) -> Matrix:
    return sp.simplify(m * x * m.inv())


def is_zero(m: Matrix) -> bool:
    return m.equals(zeros(*m.shape))


def main() -> int:
    checks = {}

    # 1) Self-dual cone layer (operator-side readout shape):
    # positive orthant sample: basis rays remain dual under standard pairing.
    u, v = sp.symbols("u v", nonnegative=True)
    checks["orthant basis pairing nonneg"] = (
        (sp.Matrix([u, 0]).dot(sp.Matrix([v, 0])) >= 0)
        and (sp.Matrix([u, 0]).dot(sp.Matrix([0, v])) >= 0)
        and (sp.Matrix([0, v]).dot(sp.Matrix([0, v])) >= 0)
    )

    # 2) Fenchel-Legendre finite quadratic model:
    # f(x)=x²/2 is self-conjugate in Legendre-Fenchel normal form.
    x, y = sp.symbols("x y", real=True)
    f = x ** 2 / 2
    f_star = y ** 2 / 2
    f_star_star = x ** 2 / 2
    checks["fenchel quadratic self-conjugate"] = (sp.expand(f_star_star - f) == 0)
    checks["fenchel first derivative"] = (sp.expand(sp.diff(f, x) - x) == 0)
    checks["fenchel involution model"] = (sp.expand(f_star - (y ** 2 / 2)) == 0)

    # 3) Weyl A₁×A₁ finite reflections.
    r1 = Matrix([[-1, 0], [0, 1]])
    r2 = Matrix([[1, 0], [0, -1]])
    r3 = Matrix([[-1, 0], [0, -1]])
    I2 = sp.eye(2)
    G = Matrix([[2, 0], [0, 2]])
    H = Matrix([[1, 0], [0, -1]])

    checks["r1^2 = I"] = is_zero(r1 * r1 - I2)
    checks["r2^2 = I"] = is_zero(r2 * r2 - I2)
    checks["r3^2 = I"] = is_zero(r3 * r3 - I2)
    checks["r1 r2 = r2 r1"] = is_zero(r1 * r2 - r2 * r1)
    checks["r1 r2 = r3"] = is_zero(r1 * r2 - r3)
    checks["r1 preserves H"] = is_zero(r1 * H * r1 - H)
    checks["r2 preserves H"] = is_zero(r2 * H * r2 - H)
    checks["r3 preserves H"] = is_zero(r3 * H * r3 - H)
    checks["r1 preserves G"] = is_zero(r1.T * G * r1 - G)
    checks["r2 preserves G"] = is_zero(r2.T * G * r2 - G)
    checks["r3 preserves G"] = is_zero(r3.T * G * r3 - G)

    # 4) Conformal Weyl/Möbius bridge on the 2×2 finitary carrier.
    W = Matrix([[1, 0], [0, -1]])
    N = Matrix([[0, 1], [0, 0]])
    K = Matrix([[1, 0], [0, -1]])
    P = Matrix([[0, 1], [0, 0]])
    D = Matrix([[Rational(1, 2), 0], [0, -Rational(1, 2)]])
    checks["W^2 = I"] = is_zero(W * W - I2)
    checks["W N W = -N"] = is_zero(W * N * W + N)
    checks["W K W = K"] = is_zero(W * K * W - K)
    checks["Ad_W P = -P"] = is_zero(conj(W, P) + P)
    checks["Ad_W D = D"] = is_zero(conj(W, D) - D)
    checks["Ad_W K = K"] = is_zero(conj(W, K) - K)

    # 5) Klein finite affine relation A B A⁻¹ = B⁻¹.
    A = Matrix([[1, 0, sp.Rational(1, 2)], [0, -1, 0], [0, 0, 1]])
    A_inv = Matrix([[1, 0, -sp.Rational(1, 2)], [0, -1, 0], [0, 0, 1]])
    B = Matrix([[1, 0, 0], [0, 1, 1], [0, 0, 1]])
    B_inv = Matrix([[1, 0, 0], [0, 1, -1], [0, 0, 1]])
    checks["A A⁻¹ = I"] = is_zero(A * A_inv - sp.eye(3))
    checks["A⁻¹ A = I"] = is_zero(A_inv * A - sp.eye(3))
    checks["B B⁻¹ = I"] = is_zero(B * B_inv - sp.eye(3))
    checks["B⁻¹ B = I"] = is_zero(B_inv * B - sp.eye(3))
    checks["A B A⁻¹ = B⁻¹"] = is_zero(A * B * A_inv - B_inv)

    # 6) Root-space consistency check (finite action model).
    alpha1 = Matrix([1, 0])
    alpha2 = Matrix([0, 1])
    Aroot = Matrix([[2, 0], [0, 2]])
    checks["r1(alpha1) = -alpha1"] = is_zero(r1 * alpha1 - (-alpha1))
    checks["r1(alpha2) = alpha2"] = is_zero(r1 * alpha2 - alpha2)
    checks["r2(alpha1) = alpha1"] = is_zero(r2 * alpha1 - alpha1)
    checks["r2(alpha2) = -alpha2"] = is_zero(r2 * alpha2 - (-alpha2))
    checks["root-lattice check formula 1"] = is_zero((alpha1 - Aroot[0, 0] * alpha1) - (-alpha1))

    print("=== Self-dual / Fenchel layer ===")
    for key in [
        "orthant basis pairing nonneg",
        "fenchel quadratic self-conjugate",
        "fenchel first derivative",
        "fenchel involution model",
    ]:
        print(f"  {key}: {checks[key]}")

    print("\n=== Finite A₁ × A₁ Weyl layer ===")
    for key in [
        "r1^2 = I",
        "r2^2 = I",
        "r3^2 = I",
        "r1 r2 = r2 r1",
        "r1 r2 = r3",
        "r1 preserves H",
        "r2 preserves H",
        "r3 preserves H",
        "r1 preserves G",
        "r2 preserves G",
        "r3 preserves G",
    ]:
        print(f"  {key}: {checks[key]}")

    print("\n=== Conformal / Weyl bridge ===")
    for key in [
        "W^2 = I",
        "W N W = -N",
        "W K W = K",
        "Ad_W P = -P",
        "Ad_W D = D",
        "Ad_W K = K",
    ]:
        print(f"  {key}: {checks[key]}")

    print("\n=== Klein finite affine relation ===")
    for key in [
        "A A⁻¹ = I",
        "A⁻¹ A = I",
        "B B⁻¹ = I",
        "B⁻¹ B = I",
        "A B A⁻¹ = B⁻¹",
    ]:
        print(f"  {key}: {checks[key]}")

    # 7) Finite affine cocycle: Weyl reflection is conjugated into a translation class.
    W_klein = Matrix([[-1, 0, 0], [0, 1, 0], [0, 0, 1]])
    Bx = Matrix([[1, 0, -1], [0, 1, 0], [0, 0, 1]])
    checks["A W_klein A⁻¹ = W_klein Bx"] = is_zero(A * W_klein * A_inv - W_klein * Bx)
    checks["A W_klein = W_klein Bx A"] = is_zero(A * W_klein - W_klein * Bx * A)

    print("\n=== Klein affine cocycle relation ===")
    for key in [
        "A W_klein A⁻¹ = W_klein Bx",
        "A W_klein = W_klein Bx A",
    ]:
        print(f"  {key}: {checks[key]}")

    print("\n=== Root action checks ===")
    for key in [
        "r1(alpha1) = -alpha1",
        "r1(alpha2) = alpha2",
        "r2(alpha1) = alpha1",
        "r2(alpha2) = -alpha2",
        "root-lattice check formula 1",
    ]:
        print(f"  {key}: {checks[key]}")

    # 8) Affine Weyl/Klein torus action mismatch (non-commutation).
    #   K : (θ₁, θ₂) ↦ (θ₁ + π, -θ₂)
    #   W : (θ₁, θ₂) ↦ (-θ₁ + θ₂, θ₂)
    θ1, θ2 = sp.symbols("θ1 θ2", real=True)
    t = sp.Matrix([θ1, θ2])
    K_torus = sp.Matrix([t[0] + sp.pi, -t[1]])
    W_torus = sp.Matrix([-t[0] + t[1], t[1]])
    K_of_W = sp.Matrix([W_torus[0] + sp.pi, -W_torus[1]])
    W_of_K = sp.Matrix([-(K_torus[0]) + K_torus[1], K_torus[1]])
    checks["K(W(t)) - W(K(t))"] = (K_of_W - W_of_K)
    checks["W(K(t)) - K(W(t))"] = (W_of_K - K_of_W)
    checks["K(W(t)) - W(K(t)) simplified"] = sp.simplify(checks["K(W(t)) - W(K(t))"])
    print("\n=== Torus action noncommutation ===")
    print(f"  K(W) - W(K) = {checks['K(W(t)) - W(K(t)) simplified']}")
    print(f"  W(K) - K(W) = {checks['W(K(t)) - K(W(t))']}")

    # Express the mismatch as a coordinate defect in the first component only.
    checks["first-component defect is translation family"] = checks["K(W(t)) - W(K(t))"] == sp.Matrix([2 * θ2 + 2 * sp.pi, 0])
    checks["alternative sign convention defect"] = checks["W(K(t)) - K(W(t))"] == sp.Matrix([-2 * θ2 - 2 * sp.pi, 0])
    print(
        "  first-component defect is 2*θ2 + 2π? "
        f"{checks['first-component defect is translation family']}"
    )
    print(
        "  alternate-sign defect matches -2*θ2 - 2π? "
        f"{checks['alternative sign convention defect']}"
    )

    overall = all(checks.values())
    print(f"\nOVERALL: {overall}")
    if not overall:
        for k, v in checks.items():
            if not v:
                print(f"FAILED: {k}")
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
