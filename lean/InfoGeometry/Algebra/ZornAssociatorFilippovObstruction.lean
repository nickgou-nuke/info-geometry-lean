/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Algebra.ZornPeirceMixedAssociator
import Mathlib.Basic.Real.Basic

/-!
# A Filippov obstruction for the native Zorn associator

The defect is left side minus right side of the ternary fundamental identity.
The polynomial calculation works over any commutative ring; its nonvanishing is
asserted only over the reals. This does not concern the corrected standard
derivation of an alternative algebra or a Lie algebra's nested triple product.
-/

namespace InfoGeometry.Algebra.ZornVectorMatrix

variable {R : Type*} [CommRing R]

/-- The fundamental-identity defect of the existing associator, with no new bracket. -/
def associatorFilippovDefect (x y u v w : ZornVectorMatrix R) :
    ZornVectorMatrix R :=
  sub (associator x y (associator u v w))
    (add (add (associator (associator x y u) v w)
      (associator u (associator x y v) w))
      (associator u v (associator x y w)))

/-- The left side of the fundamental identity vanishes on the selected five inputs. -/
theorem associator_filippov_UUUVV_lhs :
    associator (U 0 : ZornVectorMatrix R) (U 1)
      (associator (U 2) (V 0) (V 1)) = zero := by
  ext i <;> (try fin_cases i) <;>
    norm_num [associator, sub, add, neg, mul, U, V, zero,
      ZornVec3.dot, ZornVec3.cross, ZornVec3.basis, Fin.sum_univ_three]

/-- The three right-side terms sum to negative four times the upper basis vector. -/
theorem associator_filippov_UUUVV_rhs :
    add (add
      (associator (associator (U 0 : ZornVectorMatrix R) (U 1) (U 2)) (V 0) (V 1))
      (associator (U 2) (associator (U 0) (U 1) (V 0)) (V 1)))
      (associator (U 2) (V 0) (associator (U 0) (U 1) (V 1))) =
        smul (-4 : R) (U 2) := by
  ext i <;> (try fin_cases i) <;>
    norm_num [associator, sub, add, neg, mul, smul, U, V,
      ZornVec3.dot, ZornVec3.cross, ZornVec3.basis, Fin.sum_univ_three]

/-- Exact polynomial obstruction, without characteristic or nontriviality assumptions. -/
theorem associatorFilippovDefect_UUUVV :
    associatorFilippovDefect (U 0 : ZornVectorMatrix R) (U 1) (U 2) (V 0) (V 1) =
      smul (4 : R) (U 2) := by
  unfold associatorFilippovDefect
  rw [associator_filippov_UUUVV_lhs, associator_filippov_UUUVV_rhs]
  ext i <;> (try fin_cases i) <;> simp [sub, add, neg, zero, smul, U, ZornVec3.basis]

/-- The selected Filippov defect vanishes exactly when the coefficient `4`
vanishes in the base ring. This classifies the characteristic boundary for
this witness; it does not assert the universal Filippov identity when `4 = 0`.-/
theorem associatorFilippovDefect_UUUVV_eq_zero_iff_four_eq_zero :
    associatorFilippovDefect (U 0 : ZornVectorMatrix R) (U 1) (U 2) (V 0) (V 1) = zero ↔
      (4 : R) = 0 := by
  rw [associatorFilippovDefect_UUUVV]
  constructor
  · intro h
    have hv := congrArg (fun X : ZornVectorMatrix R => X.v 2) h
    simpa [smul, U, ZornVec3.basis, zero] using hv
  · intro hfour
    rw [hfour]
    simp [smul, U, ZornVec3.basis, zero]

/-- Over the reals the displayed obstruction is genuinely nonzero. -/
theorem associatorFilippovDefect_real_ne_zero :
    associatorFilippovDefect (U 0 : ZornVectorMatrix ℝ) (U 1) (U 2) (V 0) (V 1) ≠
      zero := by
  rw [associatorFilippovDefect_UUUVV]
  intro h
  have hv := congrArg (fun X : ZornVectorMatrix ℝ => X.v 2) h
  norm_num [smul, U, ZornVec3.basis, zero] at hv

/-- The Zorn associator on the real split octonions is not a Filippov bracket. -/
theorem associator_not_filippov_real :
    ¬ (∀ x y u v w : ZornVectorMatrix ℝ,
      associator x y (associator u v w) =
        add (add (associator (associator x y u) v w)
          (associator u (associator x y v) w))
          (associator u v (associator x y w))) := by
  intro h
  apply associatorFilippovDefect_real_ne_zero
  unfold associatorFilippovDefect
  rw [h (U 0) (U 1) (U 2) (V 0) (V 1)]
  ext i <;> simp [sub, add, neg, zero]

end InfoGeometry.Algebra.ZornVectorMatrix
