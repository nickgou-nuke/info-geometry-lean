import InfoGeometry.Lie.SplitOctonionCircularPeirceBasis

/-!
# Circular Norm Normal Form and Null Cone

This file formalizes the purely algebraic translation of the split-octonion norm
into its circular/Witt coordinate normal form.

In Gogberashvili-Sakhelashvili (arXiv:1506.01012v2), the split-octonion norm is
`N² = ω² - λ² + x² - c²t²`.
Using the circular coordinates:
`α = ω + ct`
`β = ω - ct`
`y = λ + x`
`z = λ - x`

The norm identically becomes `N² = αβ - z·y`. The null-cone is defined by `N² = 0`,
which is equivalently `αβ = z·y`.
-/

namespace InfoGeometry.Lie.SplitOctonionCircularNormCone

open Finset

/-- The exact translation of the Gogberashvili-Sakhelashvili norm into the Witt normal form. -/
theorem gogberashvili_norm_eq_circular (ω t : ℝ) (c : ℝ) (lam x : Fin 3 → ℝ) :
    ω^2 - (∑ i, lam i * lam i) + (∑ i, x i * x i) - c^2 * t^2 =
      (ω + c * t) * (ω - c * t) - ∑ i, (lam i - x i) * (lam i + x i) := by
  calc
    ω^2 - (∑ i, lam i * lam i) + (∑ i, x i * x i) - c^2 * t^2
      = ω^2 - c^2 * t^2 - ((∑ i, lam i * lam i) - (∑ i, x i * x i)) := by ring
    _ = (ω + c * t) * (ω - c * t) - ∑ i, (lam i - x i) * (lam i + x i) := by
      congr 1
      · ring
      · rw [← sum_sub_distrib]
        apply sum_congr rfl
        intro i _
        ring

/-- The zero-norm cone equivalence. -/
theorem gogberashvili_zeroNorm_iff_circularCone (ω t : ℝ) (c : ℝ) (lam x : Fin 3 → ℝ) :
    ω^2 - (∑ i, lam i * lam i) + (∑ i, x i * x i) - c^2 * t^2 = 0 ↔
      (ω + c * t) * (ω - c * t) = ∑ i, (lam i - x i) * (lam i + x i) := by
  rw [gogberashvili_norm_eq_circular]
  exact sub_eq_zero

open InfoGeometry.Lie.SplitOctonionCircularPeirceBasis
open InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis
open InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates
open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge

abbrev CZ := CanonicalZorn

/-- The norm in circular Witt coordinates. -/
theorem circularNorm_eq (X : CZ) :
    InfoGeometry.Algebra.Zorn.ZornMatrix.detZ X =
      circularCoordinate (cartesianZornLinearEquiv.symm X) 0 * circularCoordinate (cartesianZornLinearEquiv.symm X) 4 -
      ∑ i : Fin 3, circularCoordinate (cartesianZornLinearEquiv.symm X) ⟨i.val + 1, by omega⟩ *
        circularCoordinate (cartesianZornLinearEquiv.symm X) ⟨i.val + 5, by omega⟩ := by
  rw [circularPeirceBasis_norm_formula]
  have h : ∑ i : Fin 3, circularCoordinate (cartesianZornLinearEquiv.symm X) ⟨i.val + 1, by omega⟩ *
        circularCoordinate (cartesianZornLinearEquiv.symm X) ⟨i.val + 5, by omega⟩ =
      circularCoordinate (cartesianZornLinearEquiv.symm X) 1 * circularCoordinate (cartesianZornLinearEquiv.symm X) 5 +
      circularCoordinate (cartesianZornLinearEquiv.symm X) 2 * circularCoordinate (cartesianZornLinearEquiv.symm X) 6 +
      circularCoordinate (cartesianZornLinearEquiv.symm X) 3 * circularCoordinate (cartesianZornLinearEquiv.symm X) 7 := by
    rw [Fin.sum_univ_three]; rfl
  rw [h]

/-- The zero-norm cone in circular Witt coordinates. -/
theorem circularNorm_zero_iff (X : CZ) :
    InfoGeometry.Algebra.Zorn.ZornMatrix.detZ X = 0 ↔
      circularCoordinate (cartesianZornLinearEquiv.symm X) 0 * circularCoordinate (cartesianZornLinearEquiv.symm X) 4 =
      ∑ i : Fin 3, circularCoordinate (cartesianZornLinearEquiv.symm X) ⟨i.val + 1, by omega⟩ *
        circularCoordinate (cartesianZornLinearEquiv.symm X) ⟨i.val + 5, by omega⟩ := by
  rw [circularNorm_eq]
  exact sub_eq_zero

end InfoGeometry.Lie.SplitOctonionCircularNormCone
