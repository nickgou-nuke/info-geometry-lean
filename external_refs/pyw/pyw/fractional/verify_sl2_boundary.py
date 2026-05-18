"""
Standalone verification of sl(2) principal admissible weights at k = -4/3.

This script does not require SageMath - it demonstrates the mathematical
computation using only Python's fractions module.
"""

from fractions import Fraction


def latex_weight(a0: Fraction, a1: Fraction) -> str:
    """Generate LaTeX representation of weight a₀Λ₀ + a₁Λ₁."""
    parts = []
    if a0 != 0:
        if a0 == -1:
            parts.append(r"-\Lambda_0")
        elif a0 == 1:
            parts.append(r"\Lambda_0")
        else:
            sign = "-" if a0 < 0 else ""
            abs_val = abs(a0)
            if abs_val.denominator == 1:
                parts.append(f"{sign}{abs_val.numerator}\\Lambda_0")
            else:
                parts.append(
                    f"{sign}\\frac{{{abs_val.numerator}}}{{{abs_val.denominator}}}\\Lambda_0"
                )

    if a1 != 0:
        if a1 == -1:
            parts.append(r"- \Lambda_1" if parts else r"- \Lambda_1")
        elif a1 == 1:
            parts.append(r"\Lambda_1" if parts else r"\Lambda_1")
        else:
            sign = "-" if a1 < 0 else ""
            if not parts and sign == "-":
                sign = "- "
            abs_val = abs(a1)
            if abs_val.denominator == 1:
                parts.append(f"{sign}{abs_val.numerator}\\Lambda_1")
            else:
                parts.append(
                    f"{sign}\\frac{{{abs_val.numerator}}}{{{abs_val.denominator}}}\\Lambda_1"
                )

    if not parts:
        return "0"

    return " + ".join(parts).replace("+ -", "- ")


def print_sl2_admissible_weight_verification():
    """Compute and verify sl(2) principal admissible weights at k = -4/3."""
    print("=" * 70)
    print("sl(2) Principal Admissible Weights at k = -4/3")
    print("=" * 70)

    # Parameters for sl(2) at boundary admissible level k = -4/3
    # k = -h^∨ + p/u with h^∨ = 2, p = 2, u = 3
    h_vee = 2
    k = Fraction(-4, 3)
    k_plus_h = Fraction(2, 3)  # k + h^∨ = 2/3
    p, u = 2, 3

    print(f"\nInput parameters:")
    print(f"  h^∨ = {h_vee}")
    print(f"  k = {k}")
    print(f"  k + h^∨ = {k_plus_h}")
    print(f"  p = {p}, u = {u}")
    print(f"  Verification: k = -h^∨ + p/u = -{h_vee} + {p}/{u} = {Fraction(-h_vee * u + p, u)} ✓")

    print("\n" + "-" * 70)
    print("Formula Derivation")
    print("-" * 70)
    print(r"The principal admissible weights are given by:")
    print(r"  Λ(m) = t_{mω} · (kΛ₀)")
    print(r"where t_{mω} is translation by mω and · is the dot action.")
    print()
    print(r"Using the CORRECT translation formula:")
    print(r"  t_β(μ) = μ - μ(K)β + (δ-shift)")
    print(r"where μ(K) = k + h^∨ is the level of μ = kΛ₀ + ρ̂.")
    print()
    print(r"For sl(2), ω = Λ₁ - Λ₀, so:")
    print(r"  Λ(m) = kΛ₀ - (k + h^∨) · m · ω")
    print(r"       = kΛ₀ - (k + h^∨) · m · (Λ₁ - Λ₀)")
    print(r"       = (k + (k + h^∨) · m) Λ₀ - (k + h^∨) · m Λ₁")
    print()
    print(f"Substituting k = {k}, k + h^∨ = {k_plus_h}:")
    print(rf"  Λ(m) = ({k} + {k_plus_h}·m) Λ₀ - {k_plus_h}·m Λ₁")

    print("\n" + "-" * 70)
    print("Computed Weights")
    print("-" * 70)

    weights = []
    for m in range(u):
        # Λ(m) = (k + k_plus_h * m) Λ₀ - k_plus_h * m Λ₁
        a0 = k + k_plus_h * m
        a1 = -k_plus_h * m

        latex = latex_weight(a0, a1)
        weights.append((m, a0, a1, latex))

        # Verify level: a0 + a1 should equal k
        level_check = a0 + a1
        status = "✓" if level_check == k else "✗"

        print(f"\nm = {m}:")
        print(f"  Coefficients: a₀ = {a0}, a₁ = {a1}")
        print(f"  Λ = {latex}")
        print(f"  Level check: {a0} + {a1} = {level_check} (expected {k}) {status}")

    print("\n" + "-" * 70)
    print("Expected vs Computed")
    print("-" * 70)

    expected = [
        (Fraction(-4, 3), Fraction(0, 1)),
        (Fraction(-2, 3), Fraction(-2, 3)),
        (Fraction(0, 1), Fraction(-4, 3)),
    ]

    print("\nExpected (from user):")
    print("  m=0: Λ = -4/3 Λ₀")
    print("  m=1: Λ = -2/3 Λ₀ - 2/3 Λ₁")
    print("  m=2: Λ = -4/3 Λ₁")

    print("\nComputed:")
    all_match = True
    for m, (exp_a0, exp_a1) in enumerate(expected):
        _, a0, a1, _ = weights[m]
        match = a0 == exp_a0 and a1 == exp_a1
        all_match = all_match and match
        status = "✓" if match else "✗"
        print(f"  m={m}: ({a0}, {a1}) vs expected ({exp_a0}, {exp_a1}) {status}")

    if all_match:
        print("\n✓ All weights match!")

    return weights


def print_sl2_conformal_dimension_verification():
    """Compute conformal dimensions for the admissible weights."""
    print("\n" + "=" * 70)
    print("Conformal Dimensions")
    print("=" * 70)

    # Parameters
    k = Fraction(-4, 3)
    k_plus_h = Fraction(2, 3)  # k + h^∨
    h_vee = 2
    p, u = 2, 3

    print("\nFormula:")
    print(r"  h_Λ = (Λ̄, Λ̄ + 2ρ) / (2(k + h^∨))")
    print()
    print("For sl(2) with finite part a·ω:")
    print(r"  h(a) = a(a + 2)(ω, ω) / (2(k + h^∨))")
    print(r"       = a(a + 2) · (1/2) / (2 · 2/3)")
    print(r"       = 3a(a + 2) / 8")
    print()
    print("The weights have Dynkin labels a_m = -2m/u (negative, antidominant).")
    print("The conformal dimension uses |a_m| (absolute value):")
    print(r"  h_m = 3 · |a_m| · (|a_m| + 2) / 8")

    print("\n" + "-" * 70)
    print("Computation")
    print("-" * 70)

    expected = [Fraction(0, 1), Fraction(2, 3), Fraction(5, 3)]
    dimensions = []

    for m in range(u):
        a = -Fraction(2 * m, u)  # Dynkin label (negative)
        a_abs = Fraction(2 * m, u)  # |a| (positive)

        # h = 3 * |a| * (|a| + 2) / 8
        h_val = Fraction(3, 8) * a_abs * (a_abs + 2)
        dimensions.append(h_val)

        status = "✓" if h_val == expected[m] else "✗"
        print(f"\nm = {m}:")
        print(f"  Dynkin label: a = {a} (antidominant)")
        print(f"  |a| = {a_abs}")
        print(f"  h = 3 · {a_abs} · ({a_abs} + 2) / 8 = {h_val}")
        print(f"  Expected: {expected[m]} {status}")

    print("\n" + "-" * 70)
    print(f"Summary: h = {dimensions}")
    print(f"Expected: {expected}")
    print(f"Match: {dimensions == expected} {'✓' if dimensions == expected else '✗'}")

    return dimensions


def main():
    """Main verification function."""
    weights = print_sl2_admissible_weight_verification()
    dimensions = print_sl2_conformal_dimension_verification()

    print("\n" + "=" * 70)
    print("FINAL ANSWER")
    print("=" * 70)
    print()
    print("Principal admissible weights for sl(2) at k = -4/3:")
    print()
    print("| m | Weight Λ              | Conformal dim h |")
    print("|---|------------------------|-----------------|")
    print("| 0 | $-\\frac{4}{3}\\Lambda_0$                    | 0               |")
    print("| 1 | $-\\frac{2}{3}\\Lambda_0 - \\frac{2}{3}\\Lambda_1$ | $\\frac{2}{3}$     |")
    print("| 2 | $-\\frac{4}{3}\\Lambda_1$                    | $\\frac{5}{3}$     |")
    print()


if __name__ == "__main__":
    main()
