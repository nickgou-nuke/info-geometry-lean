import InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.L2Multiplier
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Measurable `L²` boundary multiplier bridge

The raw boundary-symbol owner is pointwise.  This file is the measured bridge:
an already-formed `L∞` class acts by Mathlib's canonical `L²` multiplier.
No representative-level measurability or Fredholm claim is introduced here.
-/

open scoped ENNReal
open MeasureTheory

noncomputable section

namespace InfoGeometry.Topology.BoundaryMultiplierL2Bridge

open InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.L2Multiplier

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

def unitNormMulOp (a : Linftyc α μ) (ha : ‖a‖ = 1) :
    L2c α μ →L[ℂ] L2c α μ :=
  mulOp a

theorem unitNormMulOp_apply (a : Linftyc α μ) (ha : ‖a‖ = 1)
    (f : L2c α μ) :
    unitNormMulOp a ha f = a • f := by
  exact mulOp_apply a f

theorem norm_unitNormMulOp_apply_le (a : Linftyc α μ) (ha : ‖a‖ = 1)
    (f : L2c α μ) :
    ‖unitNormMulOp a ha f‖ ≤ ‖f‖ := by
  rw [unitNormMulOp]
  simpa [ha] using (norm_mulOp_apply_le a f)

theorem norm_unitNormMulOp_le (a : Linftyc α μ) (ha : ‖a‖ = 1) :
    ‖unitNormMulOp a ha‖ ≤ 1 := by
  rw [unitNormMulOp]
  simpa [ha] using (norm_mulOp_le a)

theorem mulOp_comp_mulOp (a b : Linftyc α μ)
    (hab : ∀ᵐ x ∂μ, a x * b x = 1) :
    (mulOp a).comp (mulOp b) = ContinuousLinearMap.id ℂ (L2c α μ) := by
  ext f
  rw [ContinuousLinearMap.comp_apply, mulOp_apply, mulOp_apply]
  have h₁ := mulOp_apply_ae a (mulOp b f)
  have h₂ := mulOp_apply_ae b f
  filter_upwards [h₁, h₂, hab] with x h₁ h₂ habx
  calc
    _ = a x * (mulOp b f) x := h₁
    _ = a x * (b x * f x) := by rw [h₂]
    _ = f x := by rw [← mul_assoc, habx, one_mul]

theorem mulOp_comp_mulOp_rev (a b : Linftyc α μ)
    (hba : ∀ᵐ x ∂μ, b x * a x = 1) :
    (mulOp b).comp (mulOp a) = ContinuousLinearMap.id ℂ (L2c α μ) := by
  exact mulOp_comp_mulOp b a hba

theorem mulOp_left_inverse_apply (a b : Linftyc α μ)
    (hab : ∀ᵐ x ∂μ, a x * b x = 1) (f : L2c α μ) :
    mulOp a (mulOp b f) = f := by
  have h := congrArg (fun T : L2c α μ →L[ℂ] L2c α μ => T f)
    (mulOp_comp_mulOp a b hab)
  simpa using h

theorem mulOp_right_inverse_apply (a b : Linftyc α μ)
    (hba : ∀ᵐ x ∂μ, b x * a x = 1) (f : L2c α μ) :
    mulOp b (mulOp a f) = f := by
  exact mulOp_left_inverse_apply b a hba f

end InfoGeometry.Topology.BoundaryMultiplierL2Bridge
