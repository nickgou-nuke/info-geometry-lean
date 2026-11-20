/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.DualNumber
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.RingTheory.Nilpotent.Basic

/-!
# Nilpotence, tripotence, and unital quotient boundaries

A nilpotent tripotent is zero in every monoid with zero. Separately, the
anticommutator equation `a * b + b * a = 1` implies that a unital ring
homomorphism killing either factor has a subsingleton codomain. This uses the
anticommutator equation itself; square-zero hypotheses are unnecessary.

The same collapse holds when a unital homomorphism kills a coefficient-one
matrix unit in any finite full matrix semiring. It does not hold for every
nonzero nilpotent: the native first-coordinate homomorphism from full
`2 × 2` matrices over `DualNumber ℝ` onto full real `2 × 2` matrices kills the
nonzero square-zero matrix with entry `ε` at `(0, 1)`. Both matrix carriers
retain their native noncommutative multiplication.
-/

noncomputable section

namespace InfoGeometry.Algebra.NilpotentQuotientBoundaries

/-- A nilpotent element satisfying the tripotent equation must vanish. -/
theorem eq_zero_of_nilpotent_tripotent
    {A : Type*} [MonoidWithZero A] {a : A}
    (hnil : IsNilpotent a) (htrip : a ^ 3 = a) : a = 0 := by
  have hsquare : IsIdempotentElem (a ^ 2) := by
    change a ^ 2 * a ^ 2 = a ^ 2
    calc
      a ^ 2 * a ^ 2 = a ^ 4 := by rw [← pow_add]
      _ = a ^ 3 * a := by rw [pow_succ]
      _ = a ^ 2 := by rw [htrip, pow_two]
  have hsquare_zero : a ^ 2 = 0 :=
    hsquare.eq_zero_of_isNilpotent (IsNilpotent.pow_succ 1 hnil)
  calc
    a = a ^ 3 := htrip.symm
    _ = a ^ 2 * a := by rw [pow_succ]
    _ = 0 := by rw [hsquare_zero, zero_mul]

/-- Killing the left factor of an anticommutator equal to one collapses a unital image. -/
theorem subsingleton_of_map_left_zero_of_anticommutator_eq_one
    {A B : Type*} [Semiring A] [Semiring B]
    (f : A →+* B) {a b : A}
    (hcar : a * b + b * a = 1) (ha : f a = 0) : Subsingleton B := by
  apply subsingleton_of_zero_eq_one
  simpa only [map_add, map_mul, map_one, ha, zero_mul, mul_zero, add_zero] using
    congrArg f hcar

/-- Killing the right factor has the same consequence; no nilpotence assumption is needed. -/
theorem subsingleton_of_map_right_zero_of_anticommutator_eq_one
    {A B : Type*} [Semiring A] [Semiring B]
    (f : A →+* B) {a b : A}
    (hcar : a * b + b * a = 1) (hb : f b = 0) : Subsingleton B := by
  exact subsingleton_of_map_left_zero_of_anticommutator_eq_one f
    ((add_comm (b * a) (a * b)).trans hcar) hb

/--
A coefficient-one matrix unit generates every diagonal unit by multiplication
on both sides. A unital homomorphism killing it therefore has a subsingleton
codomain. The conclusion holds for every finite index type and does not
require a field of coefficients or distinct indices.
-/
theorem subsingleton_of_map_matrix_unit_zero
    {A B ι : Type*} [Semiring A] [Semiring B] [Fintype ι] [DecidableEq ι]
    (f : Matrix ι ι A →+* B) (i j : ι)
    (hunit : f (Matrix.single i j (1 : A)) = 0) : Subsingleton B := by
  have hdiag (k : ι) : f (Matrix.single k k (1 : A)) = 0 := by
    calc
      f (Matrix.single k k (1 : A)) =
          f (Matrix.single k i (1 : A) * Matrix.single i j (1 : A) *
            Matrix.single j k (1 : A)) := by
              simp only [Matrix.single_mul_single_same, one_mul]
      _ = 0 := by rw [map_mul, map_mul, hunit, mul_zero, zero_mul]
  apply subsingleton_of_zero_eq_one
  simpa only [map_sum, hdiag, Finset.sum_const_zero, map_one] using
    congrArg f (Matrix.sum_single_one (m := ι) (α := A))

/-- The native coefficient projection, lifted to a unital homomorphism of full matrix rings. -/
def dualMatrixFst :
    Matrix (Fin 2) (Fin 2) (DualNumber ℝ) →+* Matrix (Fin 2) (Fin 2) ℝ :=
  (TrivSqZeroExt.fstHom ℝ ℝ ℝ).toRingHom.mapMatrix

/-- The full matrix whose only nonzero entry is `ε` at `(0, 1)`. -/
def infinitesimalMatrixUnit : Matrix (Fin 2) (Fin 2) (DualNumber ℝ) :=
  Matrix.single 0 1 DualNumber.eps

/-- The off-diagonal matrix is square-zero under native matrix multiplication. -/
theorem infinitesimalMatrixUnit_sq_zero : infinitesimalMatrixUnit ^ 2 = 0 := by
  unfold infinitesimalMatrixUnit
  rw [pow_two]
  exact Matrix.single_mul_single_of_ne _ _ _ _ (by decide) _

/-- Its `(0, 1)` coefficient has second coordinate one, so the matrix is nonzero. -/
theorem infinitesimalMatrixUnit_ne_zero : infinitesimalMatrixUnit ≠ 0 := by
  intro h
  have hentry : (DualNumber.eps : DualNumber ℝ) = 0 := by
    simpa [infinitesimalMatrixUnit] using
      congrArg (fun M : Matrix (Fin 2) (Fin 2) (DualNumber ℝ) => M 0 1) h
  have hsnd : (1 : ℝ) = 0 := by
    simpa using congrArg (fun z : DualNumber ℝ => z.snd) hentry
  exact one_ne_zero hsnd

/-- The nonzero square-zero matrix lies in the kernel of the native projection. -/
theorem dualMatrixFst_infinitesimalMatrixUnit :
    dualMatrixFst infinitesimalMatrixUnit = 0 := by
  change (Matrix.single (0 : Fin 2) (1 : Fin 2) (DualNumber.eps : DualNumber ℝ)).map
    (TrivSqZeroExt.fstHom ℝ ℝ ℝ).toRingHom = 0
  simp

/-- Every real matrix lifts entrywise through the native inclusion into dual numbers. -/
theorem dualMatrixFst_surjective : Function.Surjective dualMatrixFst := by
  intro M
  refine ⟨M.map (TrivSqZeroExt.inl : ℝ → DualNumber ℝ), ?_⟩
  ext i j
  change TrivSqZeroExt.fst (TrivSqZeroExt.inl (M i j) : DualNumber ℝ) = M i j
  rfl

/-- The image carrier is the nontrivial full real matrix ring. -/
theorem dualMatrixFst_codomain_nontrivial :
    Nontrivial (Matrix (Fin 2) (Fin 2) ℝ) := by
  infer_instance

/-- In particular, the identity survives the projection as a nonzero matrix. -/
theorem dualMatrixFst_one_ne_zero :
    dualMatrixFst 1 ≠ (0 : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [map_one]
  exact one_ne_zero

/--
The killed element is noncentral: its products with the lower matrix unit
place `ε` at different diagonal entries.
-/
theorem infinitesimalMatrixUnit_not_commute_lower_unit :
    ¬ Commute infinitesimalMatrixUnit
      (Matrix.single (1 : Fin 2) (0 : Fin 2) (1 : DualNumber ℝ)) := by
  intro h
  have hentry := congrArg
    (fun M : Matrix (Fin 2) (Fin 2) (DualNumber ℝ) => (M 0 0).snd) h.eq
  simp only [infinitesimalMatrixUnit, Matrix.single_mul_single_same, mul_one, one_mul] at hentry
  simp [Matrix.single] at hentry

end InfoGeometry.Algebra.NilpotentQuotientBoundaries
