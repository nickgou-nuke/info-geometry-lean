/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.TracialGNSRightMultiplication
import Mathlib.Analysis.CStarAlgebra.Spectrum

/-!
# Right adjoints and bounded commutators on native tracial GNS

All operators act on the existing `f.GNS`. Cyclicity proves the right adjoint
law; associativity gives opposite right composition and left/right commutation.
For self-adjoint H the actual difference L_H - R_H is self-adjoint, bounded
by 2 norm H. This is not yet a growing compatible Hamiltonian tower.
-/
noncomputable section
open scoped ComplexOrder InnerProductSpace

namespace PositiveLinearMap

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (f : A →ₚ[ℂ] ℂ)
variable (htr : ∀ a b : A, f (a * b) = f (b * a))

/-- Right multiplication reverses multiplication order under composition. -/
theorem rightMulMapGNS_mul (a b : A) :
    f.rightMulMapGNS htr (a * b) =
      (f.rightMulMapGNS htr b).comp (f.rightMulMapGNS htr a) := by
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp => apply isClosed_eq <;> fun_prop
  | ih x => simp [mul_assoc]

/-- Existing left GNS action commutes with the completed right action. -/
theorem left_rightMulMapGNS_commute (a b : A) :
    Commute (f.gnsNonUnitalStarAlgHom a) (f.rightMulMapGNS htr b) := by
  apply ContinuousLinearMap.ext
  intro x
  induction x using UniformSpace.Completion.induction_on with
  | hp => apply isClosed_eq <;> fun_prop
  | ih x => simp [mul_assoc]

/-- The adjoint of right multiplication by b is right multiplication by star b. -/
theorem rightMulMapGNS_star (b : A) :
    star (f.rightMulMapGNS htr b) = f.rightMulMapGNS htr (star b) := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff
    (f.rightMulMapGNS htr (star b)) (f.rightMulMapGNS htr b)).mpr
  intro x y
  induction x, y using UniformSpace.Completion.induction_on₂ with
  | hp => apply isClosed_eq <;> fun_prop
  | ih x y =>
    simp only [rightMulMapGNS_coe, UniformSpace.Completion.inner_coe,
      preGNS_inner_def, ofPreGNS_toPreGNS, star_mul, star_star]
    simpa only [mul_assoc] using htr b (star (f.ofPreGNS x) * f.ofPreGNS y)

/-- The actual commutator superoperator on the same completed GNS space. -/
def tracialCommutatorGNS (H : A) : f.GNS →L[ℂ] f.GNS :=
  f.gnsNonUnitalStarAlgHom H - f.rightMulMapGNS htr H

/-- Its action on dense representatives is the algebra commutator. -/
@[simp] theorem tracialCommutatorGNS_toPreGNS (H a : A) :
    f.tracialCommutatorGNS htr H (f.toPreGNS a : f.GNS) =
      (f.toPreGNS (H * a - a * H) : f.GNS) := by
  simp [tracialCommutatorGNS, map_sub, UniformSpace.Completion.coe_sub]

/-- Hermitian Hamiltonians give self-adjoint commutator superoperators.
The infinitesimal time generator would be i times this operator. -/
theorem tracialCommutatorGNS_selfAdjoint (H : A) (hH : IsSelfAdjoint H) :
    IsSelfAdjoint (f.tracialCommutatorGNS htr H) := by
  change star (f.gnsNonUnitalStarAlgHom H - f.rightMulMapGNS htr H) = _
  rw [star_sub, ← map_star, f.rightMulMapGNS_star htr, hH.star_eq]
  rfl

/-- Native left-action bound extended by density, including the zero-functional case. -/
theorem gnsNonUnitalStarAlgHom_norm_apply_le (a : A) (x : f.GNS) :
    ‖f.gnsNonUnitalStarAlgHom a x‖ ≤ ‖a‖ * ‖x‖ := by
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_le (f.gnsNonUnitalStarAlgHom a).continuous.norm
      (continuous_const.mul continuous_norm)
  | ih x =>
    have hx := (f.leftMulMapPreGNS a).le_opNorm x
    have ha := mul_le_mul_of_nonneg_right (f.leftMulMapPreGNS_norm_le a) (norm_nonneg x)
    simpa only [gnsNonUnitalStarAlgHom_apply,
      ContinuousLinearMap.completion_apply_coe, UniformSpace.Completion.norm_coe]
      using hx.trans ha

/-- No nontriviality of the GNS Hilbert space is needed for this norm estimate. -/
theorem gnsNonUnitalStarAlgHom_norm_le (a : A) : ‖f.gnsNonUnitalStarAlgHom a‖ ≤ ‖a‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    (f.gnsNonUnitalStarAlgHom_norm_apply_le a)

/-- Uniform building block for summably bounded growing commutator families. -/
theorem tracialCommutatorGNS_norm_le (H : A) :
    ‖f.tracialCommutatorGNS htr H‖ ≤ 2 * ‖H‖ := by
  calc
    ‖f.tracialCommutatorGNS htr H‖ ≤
        ‖f.gnsNonUnitalStarAlgHom H‖ + ‖f.rightMulMapGNS htr H‖ := by
          simpa only [tracialCommutatorGNS] using
            norm_sub_le (f.gnsNonUnitalStarAlgHom H) (f.rightMulMapGNS htr H)
    _ ≤ ‖H‖ + ‖H‖ := add_le_add
      (f.gnsNonUnitalStarAlgHom_norm_le H)
      (f.rightMulMapGNS_norm_le htr H)
    _ = 2 * ‖H‖ := (two_mul ‖H‖).symm

end PositiveLinearMap
