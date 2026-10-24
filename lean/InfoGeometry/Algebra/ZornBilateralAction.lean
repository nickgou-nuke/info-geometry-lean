/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.ZornAlternativeLaws

/-!
# Parenthesized bilateral maps on the existing Zorn carrier

The multiplication maps are native linear endomorphisms, whose composition is
associative even though the carrier product is not. Flexibility and Moufang
are reused from the structural owner, not reproved by coordinate expansion.
-/

namespace InfoGeometry.Algebra.ZornBilateralAction

open InfoGeometry.Algebra
open scoped BigOperators

variable {R : Type*} [CommRing R]

/-- The explicitly left-parenthesized sandwich on the native split octonions. -/
noncomputable def sandwich (k : ZornVectorMatrix R) :
    ZornVectorMatrix R →ₗ[R] ZornVectorMatrix R :=
  (R_map k).comp (L_map k)

@[simp] theorem sandwich_apply (k x : ZornVectorMatrix R) :
    sandwich k x = (k * x) * k := rfl

/-- The obstruction to commuting distinct left/right multiplication maps. -/
theorem left_right_defect (u v x : ZornVectorMatrix R) :
    ((R_map v).comp (L_map u) - (L_map u).comp (R_map v)) x =
      _root_.associator u x v := rfl

/-- Flexibility is exactly commutation of the same-element left/right maps. -/
theorem same_kernel_commute (k : ZornVectorMatrix R) :
    (R_map (R := R) k).comp (L_map k) = (L_map k).comp (R_map k) := by
  ext x
  change (k * x) * k = k * (x * k)
  have h := ZornVectorMatrix.associator_flexible k x
  change (k * x) * k - k * (x * k) = 0 at h
  exact sub_eq_zero.mp h

/-- Middle Moufang as an identity of actual linear endomorphisms. -/
theorem middle_moufang_operator (k y : ZornVectorMatrix R) :
    (R_map (R := R) (y * k)).comp (L_map k) = (sandwich k).comp (R_map y) := by
  ext x
  change (k * x) * (y * k) = (k * (x * y)) * k
  calc
    _ = k * ((x * y) * k) := ZornVectorMatrix.middle_moufang k x y
    _ = _ := (congrArg (fun f : ZornVectorMatrix R →ₗ[R] ZornVectorMatrix R => f (x * y))
      (same_kernel_commute k)).symm

/-- Finite-sum transport, with no claim of analytic convolution. -/
theorem finite_sum_transport {ι : Type*} (s : Finset ι) (k : ZornVectorMatrix R)
    (x y : ι → ZornVectorMatrix R) :
    (∑ i ∈ s, (k * x i) * (y i * k)) = sandwich k (∑ i ∈ s, x i * y i) := by
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact congrArg (fun f : ZornVectorMatrix R →ₗ[R] ZornVectorMatrix R => f (x i))
    (middle_moufang_operator k (y i))

/-- Distinct kernels need not commute: a native nonzero associator is the witness. -/
theorem distinct_kernels_do_not_commute [Nontrivial R] :
    (R_map (R := R) (ZornVectorMatrix.U 2)).comp (L_map (ZornVectorMatrix.U 0)) ≠
      (L_map (ZornVectorMatrix.U 0)).comp (R_map (ZornVectorMatrix.U 2)) := by
  intro heq
  have h := congrArg (fun f : ZornVectorMatrix R →ₗ[R] ZornVectorMatrix R =>
    f (ZornVectorMatrix.U 1)) heq
  apply ZornVectorMatrix.associator_U_zero_U_one_U_two_ne_zero (R := R)
  change ((ZornVectorMatrix.U 0 * ZornVectorMatrix.U 1) * ZornVectorMatrix.U 2 -
    ZornVectorMatrix.U 0 * (ZornVectorMatrix.U 1 * ZornVectorMatrix.U 2)) = 0
  exact sub_eq_zero.mpr h

end InfoGeometry.Algebra.ZornBilateralAction
