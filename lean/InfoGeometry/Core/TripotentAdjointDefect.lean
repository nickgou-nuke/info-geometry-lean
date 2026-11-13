/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.TripotentAdjoint

/-!
# The quartic defect of the tripotent adjoint

The polynomial `D⁴ - D²` is zero on weights `-1`, `0`, and `1`, and equals
12 times the identity on weights `-2` and `2`. The existing five-component
reconstruction therefore identifies this endomorphism with 12 times the sum
of the two extreme projectors. No extreme component is assumed to be nonzero.
-/

namespace InfoGeometry.Core.TripotentAdjoint

open InfoGeometry.Physics.Algebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- The quartic defect acts on each existing component by its scalar polynomial. -/
theorem ad_quartic_defect_apply_fiveGradeProjector {S : A}
    (hS : S * S * S = S) (k : FiveGrade) (x : A) :
    (LieAlgebra.ad ℝ A S ^ 4 - LieAlgebra.ad ℝ A S ^ 2)
        (fiveGradeProjector S k x) =
      ((fiveGradeValue k : ℝ) ^ 4 - (fiveGradeValue k : ℝ) ^ 2) •
        fiveGradeProjector S k x := by
  simp only [LinearMap.sub_apply,
    ad_pow_apply_fiveGradeProjector hS k x 4,
    ad_pow_apply_fiveGradeProjector hS k x 2, sub_smul]

/-- The corrected coefficient of the two extreme adjoint projectors is 12. -/
theorem ad_quartic_defect {S : A} (hS : S * S * S = S) :
    LieAlgebra.ad ℝ A S ^ 4 - LieAlgebra.ad ℝ A S ^ 2 =
      (12 : ℝ) • (fiveGradeProjector S .posTwo + fiveGradeProjector S .negTwo) := by
  apply LinearMap.ext
  intro x
  have hrec := fiveGrade_recompose_decompose S x
  change fiveGradeProjector S .negTwo x + fiveGradeProjector S .negOne x +
      fiveGradeProjector S .zero x + fiveGradeProjector S .posOne x +
      fiveGradeProjector S .posTwo x = x at hrec
  calc
    (LieAlgebra.ad ℝ A S ^ 4 - LieAlgebra.ad ℝ A S ^ 2) x =
        (LieAlgebra.ad ℝ A S ^ 4 - LieAlgebra.ad ℝ A S ^ 2)
          (fiveGradeProjector S .negTwo x + fiveGradeProjector S .negOne x +
            fiveGradeProjector S .zero x + fiveGradeProjector S .posOne x +
            fiveGradeProjector S .posTwo x) := by rw [hrec]
    _ = (12 : ℝ) • fiveGradeProjector S .negTwo x +
        (12 : ℝ) • fiveGradeProjector S .posTwo x := by
      simp only [map_add, ad_quartic_defect_apply_fiveGradeProjector hS]
      norm_num [fiveGradeValue]
    _ = ((12 : ℝ) •
        (fiveGradeProjector S .posTwo + fiveGradeProjector S .negTwo)) x := by
      simp only [LinearMap.smul_apply, LinearMap.add_apply, smul_add]
      exact add_comm _ _

end InfoGeometry.Core.TripotentAdjoint
