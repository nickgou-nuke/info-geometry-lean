/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal

/-!
# Bounded right multiplication on the native tracial GNS space

Trace cyclicity preserves the native PreGNS seminorm under star. The existing
left multiplication estimate therefore bounds right multiplication, which extends
to the same native GNS completion. No faithful-state or normalization premise,
new Hilbert carrier, or normed instance on seminormed PreGNS is introduced.
-/
noncomputable section
open scoped ComplexOrder

namespace PositiveLinearMap

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (f : A →ₚ[ℂ] ℂ)

/-- The operator-norm bound already supplied by the native left-action construction. -/
theorem leftMulMapPreGNS_norm_le (a : A) : ‖f.leftMulMapPreGNS a‖ ≤ ‖a‖ := by
  unfold leftMulMapPreGNS
  exact LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _

/-- Traciality makes star preserve the native PreGNS seminorm. -/
theorem tracial_preGNS_star_norm (htr : ∀ a b : A, f (a * b) = f (b * a)) (a : A) :
    ‖f.toPreGNS (star a)‖ = ‖f.toPreGNS a‖ := by
  rw [preGNS_norm_def, preGNS_norm_def]
  simp only [ofPreGNS_toPreGNS, star_star]
  exact congrArg (fun z : ℂ => Real.sqrt z.re) (htr a (star a))

/-- Right multiplication is bounded by the same algebra norm as left multiplication. -/
theorem tracial_preGNS_right_mul_norm_le
    (htr : ∀ a b : A, f (a * b) = f (b * a)) (a b : A) :
    ‖f.toPreGNS (a * b)‖ ≤ ‖b‖ * ‖f.toPreGNS a‖ := by
  calc
    ‖f.toPreGNS (a * b)‖ = ‖f.toPreGNS (star (a * b))‖ :=
      (f.tracial_preGNS_star_norm htr (a * b)).symm
    _ = ‖f.leftMulMapPreGNS (star b) (f.toPreGNS (star a))‖ := by
      simp only [star_mul, leftMulMapPreGNS_apply, ofPreGNS_toPreGNS]
    _ ≤ ‖f.leftMulMapPreGNS (star b)‖ * ‖f.toPreGNS (star a)‖ :=
      (f.leftMulMapPreGNS (star b)).le_opNorm _
    _ ≤ ‖star b‖ * ‖f.toPreGNS (star a)‖ :=
      mul_le_mul_of_nonneg_right (f.leftMulMapPreGNS_norm_le (star b)) (norm_nonneg _)
    _ = ‖b‖ * ‖f.toPreGNS a‖ := by
      rw [norm_star, f.tracial_preGNS_star_norm htr]

/-- Algebraic right multiplication on Mathlib's original PreGNS type. -/
def rightMulLinearPreGNS (b : A) : f.PreGNS →ₗ[ℂ] f.PreGNS where
  toFun x := f.toPreGNS (f.ofPreGNS x * b)
  map_add' x y := by simp only [map_add, add_mul]
  map_smul' c x := by simp only [map_smul, smul_mul_assoc, RingHom.id_apply]

/-- The bounded right action, using trace only to prove continuity. -/
def rightMulMapPreGNS (htr : ∀ a b : A, f (a * b) = f (b * a)) (b : A) :
    f.PreGNS →L[ℂ] f.PreGNS :=
  (f.rightMulLinearPreGNS b).mkContinuous ‖b‖ (by
    intro x
    change ‖f.toPreGNS (f.ofPreGNS x * b)‖ ≤ ‖b‖ * ‖x‖
    simpa only [toPreGNS_ofPreGNS] using
      f.tracial_preGNS_right_mul_norm_le htr (f.ofPreGNS x) b)

@[simp] theorem rightMulMapPreGNS_apply
    (htr : ∀ a b : A, f (a * b) = f (b * a)) (b : A) (x : f.PreGNS) :
    f.rightMulMapPreGNS htr b x = f.toPreGNS (f.ofPreGNS x * b) := rfl

theorem rightMulMapPreGNS_norm_le
    (htr : ∀ a b : A, f (a * b) = f (b * a)) (b : A) :
    ‖f.rightMulMapPreGNS htr b‖ ≤ ‖b‖ := by
  unfold rightMulMapPreGNS
  exact LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _

/-- Extend to Mathlib's existing GNS completion, without changing its carrier. -/
def rightMulMapGNS (htr : ∀ a b : A, f (a * b) = f (b * a)) (b : A) :
    f.GNS →L[ℂ] f.GNS :=
  (f.rightMulMapPreGNS htr b).completion

@[simp] theorem rightMulMapGNS_coe
    (htr : ∀ a b : A, f (a * b) = f (b * a)) (b : A) (x : f.PreGNS) :
    f.rightMulMapGNS htr b (x : f.GNS) =
      (f.toPreGNS (f.ofPreGNS x * b) : f.GNS) := by
  simp [rightMulMapGNS]

/-- Completed action on actual algebra representatives. -/
@[simp] theorem rightMulMapGNS_toPreGNS
    (htr : ∀ a b : A, f (a * b) = f (b * a)) (b a : A) :
    f.rightMulMapGNS htr b (f.toPreGNS a : f.GNS) = (f.toPreGNS (a * b) : f.GNS) := by
  simp

/-- The same pointwise bound survives completion, including null vectors. -/
theorem rightMulMapGNS_norm_apply_le
    (htr : ∀ a b : A, f (a * b) = f (b * a)) (b : A) (x : f.GNS) :
    ‖f.rightMulMapGNS htr b x‖ ≤ ‖b‖ * ‖x‖ := by
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_le (f.rightMulMapGNS htr b).continuous.norm
      (continuous_const.mul continuous_norm)
  | ih x =>
    have hx := (f.rightMulMapPreGNS htr b).le_opNorm x
    have hb := mul_le_mul_of_nonneg_right (f.rightMulMapPreGNS_norm_le htr b) (norm_nonneg x)
    simpa only [rightMulMapGNS, ContinuousLinearMap.completion_apply_coe,
      UniformSpace.Completion.norm_coe] using hx.trans hb

theorem rightMulMapGNS_norm_le
    (htr : ∀ a b : A, f (a * b) = f (b * a)) (b : A) :
    ‖f.rightMulMapGNS htr b‖ ≤ ‖b‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (f.rightMulMapGNS_norm_apply_le htr b)

end PositiveLinearMap
