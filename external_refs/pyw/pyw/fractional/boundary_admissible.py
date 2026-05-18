"""
Boundary admissible weights computation for affine Kac-Moody algebras.

This module implements the computation of principal admissible weights at
boundary admissible levels, following the Kac-Wakimoto construction.

References:
    - Kac, V. G., Wakimoto, M. "On rationality of W-algebras"
    - Shan, D., Xie, D., Yan, W. "Mirror symmetry for circle compactified 4d N=2 SCFTs"
"""

from fractions import Fraction
from typing import Any, List, Tuple, Union

try:
    from sage.all import Integer, RootSystem, Rational  # type: ignore
except ImportError:
    # Fallback for environments without SageMath
    Integer = int
    RootSystem = None
    Rational = Fraction


class BoundaryAdmissibleWeights:
    """
    Compute principal admissible weights at boundary admissible levels.

    For a fractional level k = -h^∨ + p/u (with p = h^∨ for boundary case),
    the principal admissible weights are given by:

        Λ(m) = t_{mω} · (kΛ₀)  for m = 0, 1, ..., u-1

    where t_{mω} is translation by m times the fundamental coweight ω,
    and the dot action is: w · λ = w(λ + ρ̂) - ρ̂.

    The correct translation formula for the dot action is:
        t_β(μ) = μ - μ(K)β + (δ-shift)

    NOT: t_β(μ) = μ + μ(K)β  (wrong sign!)

    For sl(2) with k = -4/3:
        - h^∨ = 2, k + h^∨ = 2/3, u = 3
        - ω = Λ₁ - Λ₀ (fundamental coweight in weight notation)
        - ρ̂ = Λ₀ + Λ₁

    Results:
        m=0: Λ = -4/3 Λ₀
        m=1: Λ = -2/3 Λ₀ - 2/3 Λ₁
        m=2: Λ = -4/3 Λ₁
    """

    def __init__(self, cartan_type: Union[list, tuple], p: int, u: int) -> None:
        """
        Initialize boundary admissible weights computation.

        Parameters
        ----------
        cartan_type : List[str]
            Cartan type specification, e.g., ['A', 1, 1] for affine A₁
        p : int
            Numerator in k = -h^∨ + p/u
        u : int
            Denominator in k = -h^∨ + p/u
        """
        self.cartan_type = cartan_type
        self.p = p
        self.u = u

        # Setup root system and weight space
        self._setup()

    def _setup(self) -> None:
        """Initialize root system, weight space, and fundamental weights."""
        if RootSystem is None:
            raise ImportError("BoundaryAdmissibleWeights requires SageMath (sage.all.RootSystem)")
        # Create root system and extended weight space
        self.root_system = RootSystem(self.cartan_type)
        self.weight_space = self.root_system.weight_space(extended=True)
        self.Lambda = self.weight_space.fundamental_weights()

        # Get dual Coxeter number h^∨
        ct = self.root_system.cartan_type()
        if hasattr(ct, "dual_coxeter_number"):
            self.h_vee = Integer(ct.dual_coxeter_number())
        else:
            # Fallback for A1: h^∨ = 2
            self.h_vee = Integer(2)

        # Compute level k = -h^∨ + p/u
        self.level = Fraction(-int(self.h_vee) * self.u + self.p, self.u)

        # k + h^∨ = p/u (shifted level)
        self.k_plus_h_vee = Fraction(self.p, self.u)

        # Affine Weyl vector: ρ̂ = Λ₀ + Λ₁ for A₁^(1)
        # In general: ρ̂ = sum of all fundamental weights
        self.rho_hat = self.weight_space.rho()

    def sl2_admissible_weight_data(self) -> List[Tuple[int, Any, str]]:
        """
        Compute principal admissible weights for sl(2) at level k = -4/3.

        Returns
        -------
        List[Tuple[int, Any, str]]
            List of tuples (m, weight, latex_str) where:
            - m is the translation parameter
            - weight is the SageMath weight object
            - latex_str is LaTeX representation
        """
        # Parameters for sl(2)
        h_vee = int(self.h_vee)  # = 2 for sl(2)
        k = self.level  # k = -4/3
        k_plus_h = self.k_plus_h_vee  # k + h^∨ = 2/3

        results = []

        for m in range(self.u):
            # Compute Λ(m) = kΛ₀ - (k + h^∨) * m * ω
            # Using ω = Λ₁ - Λ₀ (for sl(2) in terms of weights)
            #
            # Derivation:
            #   Λ(m) = t_{mω} · (kΛ₀)
            #        = kΛ₀ - μ(K) * mω  (ignoring δ-shift)
            #   where μ = kΛ₀ + ρ̂, and μ(K) = k + h^∨
            #
            # So: Λ(m) = kΛ₀ - (k + h^∨) * m * (Λ₁ - Λ₀)
            #          = [k + (k + h^∨) * m] Λ₀ - (k + h^∨) * m Λ₁

            # Compute coefficients
            # Λ(m) = a₀ Λ₀ + a₁ Λ₁
            # a₀ = k + (k + h^∨) * m
            # a₁ = -(k + h^∨) * m

            a0 = Fraction(k.numerator, k.denominator) + k_plus_h * m
            a1 = -k_plus_h * m

            # Construct the weight
            weight = self._create_weight({0: a0, 1: a1})

            # Create LaTeX representation
            latex_str = self._latex_weight(a0, a1)

            results.append((m, weight, latex_str))

        return results

    def sl2_conformal_dimensions(self) -> List[Fraction]:
        """
        Compute conformal dimensions h_Λ for each admissible weight.

        For affine sl(2) with highest weight having finite part aω (Dynkin label a):
            h(a) = |a|(|a| + 2) * (ω, ω) / (2 * (k + h^∨))
                 = |a|(|a| + 2) / (4 * (k + h^∨))  (using (ω, ω) = 1/2 for sl(2))

        The weights Λ(m) have Dynkin labels a_m = -2m/u (negative, in antidominant chamber).
        The conformal dimension uses |a_m| = 2m/u.

        For k = -4/3 (i.e., k + h^∨ = 2/3):
            m=0: a = 0          → h = 0
            m=1: a = -2/3       → h = 2/3
            m=2: a = -4/3       → h = 5/3

        Returns
        -------
        List[Fraction]
            List of conformal dimensions h_Λ for each weight
        """
        dimensions = []
        for m in range(self.u):
            # Dynkin label: a = -2m/u (negative because weights are antidominant)
            # Conformal dimension uses |a|
            a_abs = Fraction(2 * m, self.u)  # |a| = 2m/u

            # Conformal dimension formula for sl(2):
            # h(|a|) = |a|(|a| + 2) * (ω, ω) / (2 * (k + h^∨))
            # With (ω, ω) = 1/2 for sl(2):
            # h = |a|(|a| + 2) / (4 * (k + h^∨))
            # With k + h^∨ = p/u:
            # h = u * |a| * (|a| + 2) / (4p)

            h_val = self.u * a_abs * (a_abs + 2) / (4 * self.p)

            dimensions.append(Fraction(h_val).limit_denominator())

        return dimensions

    def _create_weight(self, coefficients: dict) -> Any:
        """Create a weight with given fractional coefficients."""
        weight = self.weight_space.zero()
        for idx, coeff in coefficients.items():
            if isinstance(coeff, Fraction):
                frac = coeff
            elif isinstance(coeff, int):
                frac = Fraction(coeff, 1)
            else:
                frac = Fraction(coeff).limit_denominator()

            num = Integer(frac.numerator)
            den = Integer(frac.denominator)
            weight += (num / den) * self.Lambda[idx]

        return weight

    def _latex_weight(self, a0: Fraction, a1: Fraction) -> str:
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
                parts.append(r"-\Lambda_1" if parts else r"- \Lambda_1")
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


def verify_sl2_level_neg_4_3():
    """
    Verify the computation of sl(2) admissible weights at level k = -4/3.

    Expected results:
        m=0: Λ = -4/3 Λ₀          h = 0
        m=1: Λ = -2/3 Λ₀ - 2/3 Λ₁  h = 2/3
        m=2: Λ = -4/3 Λ₁          h = 5/3
    """
    print("=" * 60)
    print("sl(2) Principal Admissible Weights at k = -4/3")
    print("=" * 60)

    # For sl(2) at level k = -4/3:
    # h^∨ = 2, k = -4/3 = -2 + 2/3
    # So p = 2, u = 3 (since k = -h^∨ + p/u = -2 + 2/3)
    baw = BoundaryAdmissibleWeights(["A", 1, 1], p=2, u=3)

    print(f"\nLevel: k = {baw.level} = {float(baw.level):.4f}")
    print(f"k + h^∨ = {baw.k_plus_h_vee} = {float(baw.k_plus_h_vee):.4f}")
    print(f"h^∨ = {baw.h_vee}")
    print(f"u = {baw.u}")

    print("\n--- Principal Admissible Weights ---")
    weights = baw.sl2_admissible_weight_data()

    for m, weight, latex in weights:
        print(f"\nm = {m}:")
        print(f"  LaTeX: $\\Lambda = {latex}$")
        print(f"  Sage:  {weight}")

    print("\n--- Conformal Dimensions ---")
    dimensions = baw.sl2_conformal_dimensions()

    expected = [Fraction(0, 1), Fraction(2, 3), Fraction(5, 3)]
    print(f"\nExpected: {expected}")
    print(f"Computed: {dimensions}")
    print(f"Match: {dimensions == expected}")

    print("\n--- Verification ---")
    all_match = True
    for i, (computed, exp) in enumerate(zip(dimensions, expected)):
        match = computed == exp
        all_match = all_match and match
        status = "✓" if match else "✗"
        print(f"  h_{i}: {computed} (expected {exp}) {status}")

    if all_match:
        print("\n✓ All computations match expected values!")
    else:
        print("\n✗ Some computations do not match!")

    return weights, dimensions


if __name__ == "__main__":
    verify_sl2_level_neg_4_3()
