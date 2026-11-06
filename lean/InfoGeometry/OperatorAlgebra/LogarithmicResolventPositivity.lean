/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Abel

/-!
# Positive logarithmic resolvent residuals

For a strictly positive element `T` of a unital complex C*-algebra,
`Ring.inverse T - 1 + CFC.log T` is positive. The proof lifts the scalar
logarithm inequality by native continuous functional calculus. The ambient
algebra remains noncommutative, and no trace or simultaneous diagonalization
is used.

The specializations at `T = 1 + V` and `T = 1 - V` are exactly the two
logarithmic residual expressions in the source intake, with their domains
made explicit. Positivity alone does not identify these expressions with
Umegaki relative entropy, a Legendre dual, or a geometric curvature.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.LogarithmicResolventPositivity

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The native operator expression whose positivity is proved below. -/
def logarithmicResidual (T : A) : A := Ring.inverse T - 1 + CFC.log T

/-- The scalar inequality is lifted to the full operator carrier by CFC. -/
theorem logarithmicResidual_eq_cfc (T : A) (hT : IsStrictlyPositive T) :
    logarithmicResidual T =
      cfc (fun x : ℝ => x⁻¹ - 1 + Real.log x) T := by
  have hsa : IsSelfAdjoint T := hT.nonneg.isSelfAdjoint
  have hn : ∀ x ∈ spectrum ℝ T, x ≠ 0 := fun x hx => ne_of_gt (hT.spectrum_pos hx)
  have hi : ContinuousOn (fun x : ℝ => x⁻¹) (spectrum ℝ T) :=
    continuousOn_id.inv₀ hn
  have hl : ContinuousOn Real.log (spectrum ℝ T) :=
    Real.continuousOn_log.mono (fun x hx => hn x hx)
  rw [cfc_add T (fun x : ℝ => x⁻¹ - 1) Real.log (hi.sub continuousOn_const) hl,
    cfc_sub (fun x : ℝ => x⁻¹) (fun _ => 1) T hi continuousOn_const,
    cfc_ringInverse_id T hT.isUnit hsa, cfc_const_one ℝ T hsa]
  rfl

/-- Strict positivity gives the spectral domain needed for the logarithm. -/
theorem logarithmicResidual_nonneg (T : A) (hT : IsStrictlyPositive T) :
    0 ≤ logarithmicResidual T := by
  rw [logarithmicResidual_eq_cfc T hT]
  apply cfc_nonneg
  intro x hx
  have h := Real.one_sub_inv_le_log_of_pos (hT.spectrum_pos hx)
  linarith

omit [PartialOrder A] [StarOrderedRing A] in
/-- At the identity, the residual vanishes exactly. -/
@[simp] theorem logarithmicResidual_one : logarithmicResidual (1 : A) = 0 := by
  simp [logarithmicResidual]

omit [PartialOrder A] [StarOrderedRing A] in
/-- The plus expression is the residual at its positive-side denominator. -/
theorem logarithmicResidual_one_add (V : A) (hV : IsUnit (1 + V)) :
    logarithmicResidual (1 + V) =
      CFC.log (1 + V) - V * Ring.inverse (1 + V) := by
  have hi : (1 + V) * Ring.inverse (1 + V) = 1 :=
    Ring.mul_inverse_cancel (1 + V) hV
  unfold logarithmicResidual
  have hi' : Ring.inverse (1 + V) + V * Ring.inverse (1 + V) = 1 := by
    simpa only [add_mul, one_mul] using hi
  calc
    _ = Ring.inverse (1 + V) -
        (Ring.inverse (1 + V) + V * Ring.inverse (1 + V)) + CFC.log (1 + V) := by
          rw [hi']
    _ = _ := by abel

omit [PartialOrder A] [StarOrderedRing A] in
/-- The minus expression is the same residual at the opposite denominator. -/
theorem logarithmicResidual_one_sub (V : A) (hV : IsUnit (1 - V)) :
    logarithmicResidual (1 - V) =
      V * Ring.inverse (1 - V) + CFC.log (1 - V) := by
  have hi : (1 - V) * Ring.inverse (1 - V) = 1 :=
    Ring.mul_inverse_cancel (1 - V) hV
  unfold logarithmicResidual
  have hi' : Ring.inverse (1 - V) - V * Ring.inverse (1 - V) = 1 := by
    simpa only [sub_mul, one_mul] using hi
  calc
    _ = Ring.inverse (1 - V) -
        (Ring.inverse (1 - V) - V * Ring.inverse (1 - V)) + CFC.log (1 - V) := by
          rw [hi']
    _ = _ := by abel

/-- The plus residual on its positive-unit domain. -/
theorem plus_residual_nonneg (V : A) (hV : IsStrictlyPositive (1 + V)) :
    0 ≤ CFC.log (1 + V) - V * Ring.inverse (1 + V) := by
  rw [← logarithmicResidual_one_add V hV.isUnit]
  exact logarithmicResidual_nonneg (1 + V) hV

/-- The minus residual requires strict positivity of `1 - V`. -/
theorem minus_residual_nonneg (V : A) (hV : IsStrictlyPositive (1 - V)) :
    0 ≤ V * Ring.inverse (1 - V) + CFC.log (1 - V) := by
  rw [← logarithmicResidual_one_sub V hV.isUnit]
  exact logarithmicResidual_nonneg (1 - V) hV

/-- The scalar residual has the unique zero `x = 1` on its positive domain. -/
theorem scalar_logarithmicResidual_eq_zero_iff {x : ℝ} (hx : 0 < x) :
    x⁻¹ - 1 + Real.log x = 0 ↔ x = 1 := by
  constructor
  · intro hzero
    by_contra hne
    have hinv : x⁻¹ ≠ 1 := by
      intro hi
      apply hne
      simpa only [inv_inv, inv_one] using congrArg (fun y : ℝ => y⁻¹) hi
    have hstrict := Real.log_lt_sub_one_of_pos (inv_pos.mpr hx) hinv
    rw [Real.log_inv] at hstrict
    linarith
  · rintro rfl
    simp

/-- On the positive-unit domain, zero residual detects the identity operator.
A nonzero positive residual need not be invertible. -/
theorem logarithmicResidual_eq_zero_iff (T : A) (hT : IsStrictlyPositive T) :
    logarithmicResidual T = 0 ↔ T = 1 := by
  constructor
  · intro hzero
    have hsa : IsSelfAdjoint T := hT.nonneg.isSelfAdjoint
    have hn : ∀ x ∈ spectrum ℝ T, x ≠ 0 :=
      fun x hx => ne_of_gt (hT.spectrum_pos hx)
    have hi : ContinuousOn (fun x : ℝ => x⁻¹) (spectrum ℝ T) :=
      continuousOn_id.inv₀ hn
    have hl : ContinuousOn Real.log (spectrum ℝ T) :=
      Real.continuousOn_log.mono (fun x hx => hn x hx)
    have hf : ContinuousOn (fun x : ℝ => x⁻¹ - 1 + Real.log x)
        (spectrum ℝ T) := (hi.sub continuousOn_const).add hl
    have hcfc : cfc (fun x : ℝ => x⁻¹ - 1 + Real.log x) T =
        cfc (fun _ : ℝ => 0) T := by
      rw [cfc_const_zero, ← logarithmicResidual_eq_cfc T hT]
      exact hzero
    have hspec := eqOn_of_cfc_eq_cfc hcfc hf continuousOn_const hsa
    apply CFC.eq_one_of_spectrum_subset_one (R := ℝ) T ?_ hsa
    intro x hx
    exact Set.mem_singleton_iff.mpr
      ((scalar_logarithmicResidual_eq_zero_iff (hT.spectrum_pos hx)).mp (hspec hx))
  · rintro rfl
    exact logarithmicResidual_one

/-- The plus residual vanishes precisely at the undeformed operator. -/
theorem plus_residual_eq_zero_iff (V : A) (hV : IsStrictlyPositive (1 + V)) :
    CFC.log (1 + V) - V * Ring.inverse (1 + V) = 0 ↔ V = 0 := by
  rw [← logarithmicResidual_one_add V hV.isUnit,
    logarithmicResidual_eq_zero_iff (1 + V) hV]
  exact add_eq_left

/-- The minus residual vanishes precisely at the undeformed operator. -/
theorem minus_residual_eq_zero_iff (V : A) (hV : IsStrictlyPositive (1 - V)) :
    V * Ring.inverse (1 - V) + CFC.log (1 - V) = 0 ↔ V = 0 := by
  rw [← logarithmicResidual_one_sub V hV.isUnit,
    logarithmicResidual_eq_zero_iff (1 - V) hV]
  exact sub_eq_self

end InfoGeometry.OperatorAlgebra.LogarithmicResolventPositivity
