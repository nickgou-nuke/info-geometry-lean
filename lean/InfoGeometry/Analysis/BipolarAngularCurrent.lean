import InfoGeometry.Connection.ApolloniusOperatorConnection
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# The finite test-function current attached to the bipolar angular period

The smooth form `dTheta` is defined only on the twice-punctured plane.  The
repository does not currently contain a distribution or de Rham-current
calculus, so this file records the exact finite functional that represents the
delta-supported extension at the two punctures.  It does not identify that
functional with an exterior derivative until such a calculus is available.
-/

noncomputable section

namespace InfoGeometry.Analysis.BipolarAngularCurrent

open InfoGeometry.Connection.ApolloniusOperatorConnection

abbrev TestScalar := ℂ → ℝ
abbrev ScalarCurrent := TestScalar →ₗ[ℝ] ℝ

/-- Evaluation of a scalar test function at one puncture. -/
def pointCurrent (z : ℂ) : ScalarCurrent where
  toFun φ := φ z
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

@[simp] theorem pointCurrent_apply (z : ℂ) (φ : TestScalar) :
    pointCurrent z φ = φ z := rfl

/-- The finite current corresponding to the bipolar signed point source. -/
def bipolarAngularCurrent (α : ℝ) : ScalarCurrent :=
  (2 * Real.pi * α) • (pointCurrent 0 - pointCurrent 1)

@[simp] theorem bipolarAngularCurrent_apply (α : ℝ) (φ : TestScalar) :
    bipolarAngularCurrent α φ =
      (2 * Real.pi * α) * (φ 0 - φ 1) := by
  simp [bipolarAngularCurrent]

theorem bipolarAngularCurrent_origin_readout (α : ℝ) (φ : TestScalar)
    (hφ : φ 1 = 0) :
    bipolarAngularCurrent α φ = (2 * Real.pi * α) * φ 0 := by
  rw [bipolarAngularCurrent_apply, hφ, sub_zero]

theorem bipolarAngularCurrent_one_readout (α : ℝ) (φ : TestScalar)
    (hφ : φ 0 = 0) :
    bipolarAngularCurrent α φ = -(2 * Real.pi * α) * φ 1 := by
  rw [bipolarAngularCurrent_apply, hφ, zero_sub]
  ring

theorem bipolarAngularCurrent_diagonal_cancellation (α : ℝ) (φ : TestScalar)
    (hφ : φ 0 = φ 1) :
    bipolarAngularCurrent α φ = 0 := by
  rw [bipolarAngularCurrent_apply, hφ, sub_self, mul_zero]

theorem bipolarAngularCurrent_normalization :
    bipolarAngularCurrent 1 (fun z : ℂ => if z = 0 then 1 else 0) =
      2 * Real.pi := by
  simp [bipolarAngularCurrent_apply]

theorem bipolarAngularCurrent_signed_normalization :
    bipolarAngularCurrent 1 (fun z : ℂ => if z = 1 then 1 else 0) =
      -(2 * Real.pi) := by
  simp [bipolarAngularCurrent_apply]

end InfoGeometry.Analysis.BipolarAngularCurrent
