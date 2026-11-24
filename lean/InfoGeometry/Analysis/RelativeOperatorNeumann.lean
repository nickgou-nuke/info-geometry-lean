/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Tactic.NormNum

/-!
# Relative operator perturbations and normalized inverse bounds

If a unit `S` normalizes a reference operator by `S * P * S = 1`, a perturbation
`E` becomes `S * E * S`. Its norm controls invertibility and the actual inverse
in these coordinates. The analytic estimate is Mathlib's geometric-series
bound; the new step is its transport through the two ordered factors of `S`.

The matrix specialization uses the native continuous functional calculus over
an `RCLike` field, `S = P ^ (-(1 / 2) : ℝ)`, positive definiteness, and the
Euclidean operator norm. It explicitly converts `Ring.inverse` to the ordinary
matrix inverse. The perturbation need not commute with `P` or be self-adjoint.

The radius hypothesis is on the normalized perturbation itself. This module
does not identify this norm with a weighted field norm or prove that a
particular physical Hessian satisfies the radius hypothesis.

## Theorem contract

* Algebraic carrier: a possibly noncommutative unital ring, with `IsUnit S` and
  the normalization equation `S * P * S = 1`.
* Analytic carrier: a normed ring with summable geometric series and norm one.
* Input: `‖S * E * S‖ ≤ r`, `r < 1`; no inverse of `P + E` is assumed.
* Output: invertibility and the bound
  `‖Ring.inverse S * Ring.inverse (P + E) * Ring.inverse S‖ ≤ 1 / (1 - r)`.
* Native dependencies: `Ring.inverse_mul`, `IsUnit.one_sub_of_norm_lt_one`,
  `geom_series_eq_inverse`, `tsum_geometric_le_of_norm_lt_one`, and CFC powers.
-/

noncomputable section

namespace InfoGeometry.Analysis.RelativeOperatorNeumann

section Ring

variable {A : Type*} [Ring A] {S P E : A}

/-- Inverting the normalized operator reverses the ordered products. -/
theorem conjugated_inverse_eq (hS : IsUnit S) (hP : S * P * S = 1) :
    Ring.inverse S * Ring.inverse (P + E) * Ring.inverse S =
      Ring.inverse (1 + S * E * S) := by
  have hnorm : S * (P + E) * S = 1 + S * E * S := by
    rw [mul_add, add_mul, hP]
  calc
    Ring.inverse S * Ring.inverse (P + E) * Ring.inverse S =
        Ring.inverse (S * (P + E) * S) := by
      rw [Ring.inverse_mul (Or.inr hS), Ring.inverse_mul (Or.inl hS)]
      exact mul_assoc _ _ _
    _ = Ring.inverse (1 + S * E * S) := congrArg Ring.inverse hnorm

/-- The inverse in the original coordinates has two factors of the normalizer.
The identity also holds for Mathlib's total inverse when `P + E` is singular. -/
theorem inverse_add_eq_conjugate (hS : IsUnit S) (hP : S * P * S = 1) :
    Ring.inverse (P + E) = S * Ring.inverse (1 + S * E * S) * S := by
  rw [← conjugated_inverse_eq hS hP]
  calc
    Ring.inverse (P + E) =
        (S * Ring.inverse S) * Ring.inverse (P + E) * (Ring.inverse S * S) := by
      rw [Ring.mul_inverse_cancel S hS, Ring.inverse_mul_cancel S hS,
        one_mul, mul_one]
    _ = S * (Ring.inverse S * Ring.inverse (P + E) * Ring.inverse S) * S := by
      simp only [mul_assoc]

end Ring

section NormedRing

variable {A : Type*} [NormedRing A] [HasSummableGeomSeries A]
variable {S P E : A}

/-- Relative smallness constructs a unit; invertibility of the perturbed
operator is a conclusion. -/
theorem isUnit_add_of_relative_norm_lt_one (hS : IsUnit S)
    (hP : S * P * S = 1) (hsmall : ‖S * E * S‖ < 1) : IsUnit (P + E) := by
  have hunit : IsUnit (1 + S * E * S) := by
    simpa only [sub_neg_eq_add] using
      (IsUnit.one_sub_of_norm_lt_one (x := -(S * E * S))
        (by simpa only [norm_neg] using hsmall))
  apply hS.mul_left_iff.mp
  apply hS.mul_right_iff.mp
  simpa only [mul_add, add_mul, hP] using hunit

variable [NormOneClass A]

/-- The sharp geometric-series upper bound on the normalized inverse. -/
theorem norm_conjugated_inverse_le (hS : IsUnit S) (hP : S * P * S = 1)
    (hsmall : ‖S * E * S‖ < 1) :
    ‖Ring.inverse S * Ring.inverse (P + E) * Ring.inverse S‖ ≤
      1 / (1 - ‖S * E * S‖) := by
  rw [conjugated_inverse_eq hS hP]
  have hneg : ‖-(S * E * S)‖ < 1 := by
    simpa only [norm_neg] using hsmall
  have hgeom := tsum_geometric_le_of_norm_lt_one (-(S * E * S)) hneg
  rw [geom_series_eq_inverse _ hneg] at hgeom
  simpa only [sub_neg_eq_add, norm_neg, norm_one, sub_self, zero_add, one_div]
    using hgeom

/-- A uniform relative radius gives a uniform bound on the normalized inverse. -/
theorem norm_conjugated_inverse_le_of_le (hS : IsUnit S) (hP : S * P * S = 1)
    {r : ℝ} (hsmall : ‖S * E * S‖ ≤ r) (hr : r < 1) :
    ‖Ring.inverse S * Ring.inverse (P + E) * Ring.inverse S‖ ≤ 1 / (1 - r) := by
  exact (norm_conjugated_inverse_le hS hP (hsmall.trans_lt hr)).trans
    (one_div_le_one_div_of_le (sub_pos.mpr hr) (sub_le_sub_left hsmall 1))

/-- The radius used in a half-contraction Neumann argument gives constant `2`. -/
theorem norm_conjugated_inverse_le_two (hS : IsUnit S) (hP : S * P * S = 1)
    (hsmall : ‖S * E * S‖ ≤ 1 / 2) :
    ‖Ring.inverse S * Ring.inverse (P + E) * Ring.inverse S‖ ≤ 2 := by
  have h := norm_conjugated_inverse_le_of_le hS hP hsmall
    (by norm_num : (1 / 2 : ℝ) < 1)
  norm_num at h
  exact h

end NormedRing

section Matrix

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]
variable {P E : Matrix n n 𝕜}

private theorem matrix_conjugate_rpow_neg_half (hP : P.PosDef) :
    P ^ (-(1 / 2) : ℝ) * P * P ^ (-(1 / 2) : ℝ) = 1 := by
  have hpos := hP.isStrictlyPositive
  calc
    P ^ (-(1 / 2) : ℝ) * P * P ^ (-(1 / 2) : ℝ) =
        P ^ ((-(1 / 2) : ℝ) + 1 + (-(1 / 2) : ℝ)) := by
      rw [CFC.rpow_add hpos.isUnit, CFC.rpow_add hpos.isUnit,
        CFC.rpow_one P hpos.nonneg]
    _ = P ^ (0 : ℝ) := by norm_num
    _ = 1 := CFC.rpow_zero P hpos.nonneg

private theorem matrix_inverse_rpow_neg_half (hP : P.PosDef) :
    Ring.inverse (P ^ (-(1 / 2) : ℝ)) = P ^ (1 / 2 : ℝ) := by
  have hpos := hP.isStrictlyPositive
  have hS := hpos.isUnit.cfcRpow (-(1 / 2) : ℝ) hpos.nonneg
  have h := (Ring.inverse_mul_eq_iff_eq_mul (P ^ (-(1 / 2) : ℝ))
    (1 : Matrix n n 𝕜) (P ^ (1 / 2 : ℝ)) hS).2
      (CFC.rpow_neg_mul_rpow (1 / 2 : ℝ) hpos).symm
  simpa only [mul_one] using h

/-- A relative operator-norm ball about a positive definite real or complex
matrix consists of invertible perturbations. -/
theorem matrix_isUnit_add_of_relative_norm_lt_one (hP : P.PosDef)
    (hsmall : ‖P ^ (-(1 / 2) : ℝ) * E * P ^ (-(1 / 2) : ℝ)‖ < 1) :
    IsUnit (P + E) := by
  have hpos := hP.isStrictlyPositive
  exact isUnit_add_of_relative_norm_lt_one
    (hpos.isUnit.cfcRpow _ hpos.nonneg) (matrix_conjugate_rpow_neg_half hP) hsmall

/-- The native matrix inverse respects the relative factorization, without
commuting the base matrix past its perturbation. -/
theorem matrix_inverse_add_eq_conjugate (hP : P.PosDef) :
    (P + E)⁻¹ = P ^ (-(1 / 2) : ℝ) *
      (1 + P ^ (-(1 / 2) : ℝ) * E * P ^ (-(1 / 2) : ℝ))⁻¹ *
        P ^ (-(1 / 2) : ℝ) := by
  have hpos := hP.isStrictlyPositive
  simpa only [Matrix.nonsing_inv_eq_ringInverse] using
    (inverse_add_eq_conjugate (E := E) (hpos.isUnit.cfcRpow _ hpos.nonneg)
      (matrix_conjugate_rpow_neg_half hP))

variable [Nonempty n]

/-- The dimension-free bound for the actual matrix inverse in the metric of
the positive definite reference matrix. The norm is the Euclidean operator norm. -/
theorem matrix_norm_normalized_inverse_le (hP : P.PosDef) {r : ℝ}
    (hsmall : ‖P ^ (-(1 / 2) : ℝ) * E * P ^ (-(1 / 2) : ℝ)‖ ≤ r)
    (hr : r < 1) :
    ‖P ^ (1 / 2 : ℝ) * (P + E)⁻¹ * P ^ (1 / 2 : ℝ)‖ ≤ 1 / (1 - r) := by
  have hpos := hP.isStrictlyPositive
  have h := norm_conjugated_inverse_le_of_le
    (hpos.isUnit.cfcRpow _ hpos.nonneg) (matrix_conjugate_rpow_neg_half hP) hsmall hr
  simpa only [matrix_inverse_rpow_neg_half hP, Matrix.nonsing_inv_eq_ringInverse]
    using h

/-- A relative half-radius gives normalized inverse norm at most `2`. -/
theorem matrix_norm_normalized_inverse_le_two (hP : P.PosDef)
    (hsmall : ‖P ^ (-(1 / 2) : ℝ) * E * P ^ (-(1 / 2) : ℝ)‖ ≤ 1 / 2) :
    ‖P ^ (1 / 2 : ℝ) * (P + E)⁻¹ * P ^ (1 / 2 : ℝ)‖ ≤ 2 := by
  have h := matrix_norm_normalized_inverse_le hP hsmall
    (by norm_num : (1 / 2 : ℝ) < 1)
  norm_num at h
  exact h

end Matrix

end InfoGeometry.Analysis.RelativeOperatorNeumann
