/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.RingTheory.NonUnitalSubring.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NoncommRing

/-!
# Strict upper triangular matrices and their unipotent group

The coefficient ring is arbitrary and may be noncommutative. All mixed triple
products vanish in this native non-unital subring. The unitriangular group and
its exact commutator require no division by two.
-/

namespace InfoGeometry.Algebra.StrictUpper3

variable {A : Type*} [Ring A]

abbrev Mat3 (A : Type*) := Matrix (Fin 3) (Fin 3) A

/-- The native non-unital subring of strictly upper triangular matrices. -/
def strictUpper (A : Type*) [Ring A] : NonUnitalSubring (Mat3 A) where
  carrier := {M | ∀ i j, j ≤ i → M i j = 0}
  zero_mem' := by intro i j _; rfl
  add_mem' := by
    intro M N hM hN i j hji
    simp only [Matrix.add_apply, hM i j hji, hN i j hji, add_zero]
  neg_mem' := by
    intro M hM i j hji
    simp only [Matrix.neg_apply, hM i j hji, neg_zero]
  mul_mem' := by
    intro M N hM hN i j hji
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hki : k ≤ i
    · simp only [hM i k hki, zero_mul]
    · have hjk : j ≤ k := le_trans hji (le_of_lt (lt_of_not_ge hki))
      simp only [hN k j hjk, mul_zero]

abbrev Strict3 (A : Type*) [Ring A] := ↥(strictUpper A)

/-- The three free operator entries, with the long root in position (0,2). -/
def upper (a b c : A) : Mat3 A := !![0, a, c; 0, 0, b; 0, 0, 0]

theorem upper_mem (a b c : A) : upper a b c ∈ strictUpper A := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [upper]

def ofEntries (a b c : A) : Strict3 A := ⟨upper a b c, upper_mem a b c⟩

theorem normal_form (X : Strict3 A) :
    (X : Mat3 A) = upper ((X : Mat3 A) 0 1) ((X : Mat3 A) 1 2)
      ((X : Mat3 A) 0 2) := by
  have h := X.property
  change ∀ i j, j ≤ i → (X : Mat3 A) i j = 0 at h
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upper, h]

theorem upper_mul (a b c d e f : A) :
    upper a b c * upper d e f = upper 0 0 (a * e) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upper, Matrix.mul_apply, Fin.sum_univ_succ]

/-- Mixed triple-zero, stronger than the cube of each element being zero. -/
theorem triple_mul_zero (X Y Z : Strict3 A) :
    (X : Mat3 A) * (Y : Mat3 A) * (Z : Mat3 A) = 0 := by
  rw [normal_form X, normal_form Y, normal_form Z, upper_mul, upper_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upper]

theorem cube_zero (X : Strict3 A) : (X : Mat3 A) ^ 3 = 0 := by
  simpa only [pow_succ, pow_zero, one_mul] using triple_mul_zero X X X

/-- Integral polynomial inverse of `1 + X`. -/
def onePlusUnit (X : Strict3 A) : (Mat3 A)ˣ where
  val := 1 + (X : Mat3 A)
  inv := 1 - (X : Mat3 A) + (X : Mat3 A) * (X : Mat3 A)
  val_inv := by
    have h := triple_mul_zero X X X
    noncomm_ring [← mul_assoc, h]
  inv_val := by
    have h := triple_mul_zero X X X
    noncomm_ring [← mul_assoc, h]

@[simp] theorem onePlusUnit_val (X : Strict3 A) :
    (onePlusUnit X : Mat3 A) = 1 + (X : Mat3 A) := rfl

@[simp] theorem onePlusUnit_inv_val (X : Strict3 A) :
    (↑(onePlusUnit X)⁻¹ : Mat3 A) =
      1 - (X : Mat3 A) + (X : Mat3 A) * (X : Mat3 A) := rfl

/-- The actual unitriangular subgroup of units of the matrix ring. -/
def unitriangular (A : Type*) [Ring A] : Subgroup (Mat3 A)ˣ where
  carrier := {u | (u : Mat3 A) - 1 ∈ strictUpper A}
  one_mem' := by
    change (1 : Mat3 A) - 1 ∈ strictUpper A
    simp
  mul_mem' := by
    intro u v hu hv
    change (u : Mat3 A) * (v : Mat3 A) - 1 ∈ strictUpper A
    have heq : (u : Mat3 A) * (v : Mat3 A) - 1 =
        ((u : Mat3 A) - 1) + ((v : Mat3 A) - 1) +
          ((u : Mat3 A) - 1) * ((v : Mat3 A) - 1) := by noncomm_ring
    rw [heq]
    exact (strictUpper A).add_mem ((strictUpper A).add_mem hu hv)
      ((strictUpper A).mul_mem hu hv)
  inv_mem' := by
    intro u hu
    let X : Strict3 A := ⟨(u : Mat3 A) - 1, hu⟩
    have huX : u = onePlusUnit X := by
      apply Units.ext
      simp [X]
    rw [huX]
    change (1 - (X : Mat3 A) + (X : Mat3 A) * (X : Mat3 A)) - 1 ∈ strictUpper A
    have heq : (1 - (X : Mat3 A) + (X : Mat3 A) * (X : Mat3 A)) - 1 =
        -(X : Mat3 A) + (X : Mat3 A) * (X : Mat3 A) := by noncomm_ring
    rw [heq]
    exact (strictUpper A).add_mem ((strictUpper A).neg_mem X.property)
      ((strictUpper A).mul_mem X.property X.property)

abbrev U3 (A : Type*) [Ring A] := ↥(unitriangular A)

/-- Every unitriangular matrix is uniquely `1 + X` with `X` strictly upper. -/
def shiftEquiv : Strict3 A ≃ U3 A where
  toFun X := ⟨onePlusUnit X, by
    change (1 + (X : Mat3 A)) - 1 ∈ strictUpper A
    simpa only [add_sub_cancel_left] using X.property⟩
  invFun u := ⟨(u.val : Mat3 A) - 1, u.property⟩
  left_inv X := by apply Subtype.ext; simp
  right_inv u := by apply Subtype.ext; apply Units.ext; simp

/-- Integral unipotent multiplication in nilpotent coordinates. -/
theorem onePlusUnit_mul (X Y : Strict3 A) :
    onePlusUnit X * onePlusUnit Y = onePlusUnit (X + Y + X * Y) := by
  apply Units.ext
  change (1 + (X : Mat3 A)) * (1 + (Y : Mat3 A)) =
    1 + ((X : Mat3 A) + (Y : Mat3 A) + (X : Mat3 A) * (Y : Mat3 A))
  noncomm_ring

/-- The commutator retains the ordered coefficient product. -/
theorem onePlusUnit_commutator (X Y : Strict3 A) :
    (↑(onePlusUnit X * onePlusUnit Y * (onePlusUnit X)⁻¹ *
      (onePlusUnit Y)⁻¹) : Mat3 A) =
        1 + ((X : Mat3 A) * (Y : Mat3 A) - (Y : Mat3 A) * (X : Mat3 A)) := by
  simp only [Units.val_mul, onePlusUnit_val, onePlusUnit_inv_val]
  rw [normal_form X, normal_form Y]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upper, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply]
  all_goals noncomm_ring

/-- The first simple-root matrix, with coefficient one in position (0,1). -/
def root01 : Matrix (Fin 3) (Fin 3) A := upper 1 0 0

/-- The second simple-root matrix, with coefficient one in position (1,2). -/
def root12 : Matrix (Fin 3) (Fin 3) A := upper 0 1 0

theorem root01_mem : (root01 : Mat3 A) ∈ strictUpper A := upper_mem 1 0 0

theorem root12_mem : (root12 : Mat3 A) ∈ strictUpper A := upper_mem 0 1 0

/-- Two elements of the strict upper triangular algebra that do not commute. -/
theorem root_steps_not_commute [Nontrivial A] :
    root01 (A := A) * root12 ≠ root12 * root01 (A := A) := by
  intro h
  have h02 := congrArg (fun M : Mat3 A => M 0 2) h
  simp [root01, root12, upper] at h02

end InfoGeometry.Algebra.StrictUpper3
