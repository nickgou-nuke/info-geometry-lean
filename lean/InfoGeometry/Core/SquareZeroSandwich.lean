/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.MatrixTwoNoncommutativity
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Tactic.Module
import Mathlib.LinearAlgebra.Matrix.Trace

/-! # Symmetric sandwich action of square-zero matrices

All maps act on the full matrix algebra. No adjoint relation, positivity,
reflexivity, or commuting-generator hypothesis is assumed. The coefficients
multiplying matrices below are operator products, not scalar eigenvalues.
-/
namespace InfoGeometry.Core.SquareZeroSandwich

open Matrix

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- The paired sandwich, as a native linear endomorphism of the matrix algebra. -/
def symmSandwich (X Y : Matrix n n R) : Module.End R (Matrix n n R) where
  toFun Z := X * Z * Y + Y * Z * X
  map_add' A B := by simp only [mul_add, add_mul]; abel
  map_smul' c A := by
    simp only [mul_smul_comm, smul_mul_assoc, smul_add, RingHom.id_apply]

/-- The division-free symmetric double-commutator operator. -/
def symmDissipator (X Y : Matrix n n R) : Module.End R (Matrix n n R) where
  toFun Z := (2 : R) • symmSandwich X Y Z -
    ((X * Y + Y * X) * Z + Z * (X * Y + Y * X))
  map_add' A B := by
    simp only [map_add, smul_add, mul_add, add_mul]
    abel
  map_smul' c A := by
    simp only [map_smul, mul_smul_comm, smul_mul_assoc, smul_add, smul_sub,
      smul_comm (2 : R) c, RingHom.id_apply]

/-- Add the inner derivation by the anticommutator to the paired map. -/
def symmGenerator (X Y : Matrix n n R) : Module.End R (Matrix n n R) where
  toFun Z := (X * Y + Y * X) * Z - Z * (X * Y + Y * X) + symmDissipator X Y Z
  map_add' A B := by
    simp only [map_add, mul_add, add_mul]
    abel
  map_smul' c A := by
    simp only [map_smul, mul_smul_comm, smul_mul_assoc, smul_sub, smul_add,
      RingHom.id_apply]

/-- On the commutant of the anticommutator, the inner derivation vanishes. -/
theorem generator_eq_dissipator (X Y Z : Matrix n n R)
    (hz : (X * Y + Y * X) * Z = Z * (X * Y + Y * X)) :
    symmGenerator X Y Z = symmDissipator X Y Z := by
  change (X * Y + Y * X) * Z - Z * (X * Y + Y * X) + _ = _
  rw [hz, sub_self, zero_add]

@[simp] theorem symmSandwich_apply (X Y Z : Matrix n n R) :
    symmSandwich X Y Z = X * Z * Y + Y * Z * X := rfl

@[simp] theorem symmDissipator_apply (X Y Z : Matrix n n R) :
    symmDissipator X Y Z = (2 : R) • symmSandwich X Y Z -
      ((X * Y + Y * X) * Z + Z * (X * Y + Y * X)) := rfl

/-- Valid for arbitrary matrices, before imposing square-zero equations. -/
theorem dissipator_eq_double_commutator (X Y Z : Matrix n n R) :
    symmDissipator X Y Z =
      -((X * (Y * Z - Z * Y) - (Y * Z - Z * Y) * X) +
        (Y * (X * Z - Z * X) - (X * Z - Z * X) * Y)) := by
  simp only [symmDissipator_apply, symmSandwich_apply, two_smul]
  noncomm_ring

/-- Identity annihilation is algebraic and does not identify a vacuum state. -/
theorem dissipator_one (X Y : Matrix n n R) : symmDissipator X Y 1 = 0 := by
  simp only [dissipator_eq_double_commutator, mul_one, one_mul, sub_self,
    mul_zero, zero_mul, add_zero, neg_zero]

/-- Cyclic trace cancellation does not require nilpotency. -/
theorem trace_dissipator (X Y Z : Matrix n n R) :
    Matrix.trace (symmDissipator X Y Z) = 0 := by
  rw [dissipator_eq_double_commutator]
  simp only [Matrix.trace_neg, Matrix.trace_add, Matrix.trace_sub]
  rw [Matrix.trace_mul_comm X (Y * Z - Z * Y),
    Matrix.trace_mul_comm Y (X * Z - Z * X)]
  simp

variable {X Y : Matrix n n R}

/-- The anticommutator commutes with the first square-zero generator. -/
theorem anticomm_mul_left (hx : X * X = 0) :
    (X * Y + Y * X) * X = X * (X * Y + Y * X) := by
  have hxx : X * (X * Y) = 0 := by rw [← mul_assoc, hx, zero_mul]
  simp only [add_mul, mul_add, mul_assoc, hx, hxx, mul_zero, add_zero, zero_add]

/-- The anticommutator commutes with the second square-zero generator. -/
theorem anticomm_mul_right (hy : Y * Y = 0) :
    (X * Y + Y * X) * Y = Y * (X * Y + Y * X) := by
  simpa only [add_comm] using (anticomm_mul_left (Y := X) hy)

/-- Each seed is killed by the sandwich when that seed is square-zero. -/
theorem sandwich_left (hx : X * X = 0) : symmSandwich X Y X = 0 := by
  simp only [symmSandwich_apply, hx, zero_mul, mul_assoc, mul_zero, add_zero]

theorem sandwich_right (hy : Y * Y = 0) : symmSandwich X Y Y = 0 := by
  simp only [symmSandwich_apply, hy, zero_mul, mul_assoc, mul_zero, zero_add]

/-- Corrects the proposed nonzero sandwich action on the sum. -/
theorem sandwich_add (hx : X * X = 0) (hy : Y * Y = 0) :
    symmSandwich X Y (X + Y) = 0 := by
  rw [map_add, sandwich_left hx, sandwich_right hy, add_zero]

/-- Corrects the proposed nonzero sandwich action on the difference. -/
theorem sandwich_sub (hx : X * X = 0) (hy : Y * Y = 0) :
    symmSandwich X Y (X - Y) = 0 := by
  rw [map_sub, sandwich_left hx, sandwich_right hy, sub_self]

/-- Transport a matrix commuting with both seeds through the sandwich. -/
theorem sandwich_of_commute (Z : Matrix n n R)
    (hx : X * Z = Z * X) (hy : Y * Z = Z * Y) :
    symmSandwich X Y Z = Z * (X * Y + Y * X) := by
  rw [symmSandwich_apply, hx, hy]
  noncomm_ring

/-- The anticommutator has a quadratic sandwich image. -/
theorem sandwich_anticomm (hx : X * X = 0) (hy : Y * Y = 0) :
    symmSandwich X Y (X * Y + Y * X) = (X * Y + Y * X) * (X * Y + Y * X) :=
  sandwich_of_commute _ (anticomm_mul_left hx).symm (anticomm_mul_right hy).symm

/-- The product difference anticommutes with the first seed. -/
theorem commutator_anticomm_left (hx : X * X = 0) :
    X * (X * Y - Y * X) = -((X * Y - Y * X) * X) := by
  have hxx : X * (X * Y) = 0 := by rw [← mul_assoc, hx, zero_mul]
  simp only [mul_sub, sub_mul, mul_assoc, hx, hxx, mul_zero, zero_sub, sub_zero]

/-- The product difference anticommutes with the second seed. -/
theorem commutator_anticomm_right (hy : Y * Y = 0) :
    Y * (X * Y - Y * X) = -((X * Y - Y * X) * Y) := by
  have hyy : Y * (Y * X) = 0 := by rw [← mul_assoc, hy, zero_mul]
  simp only [mul_sub, sub_mul, mul_assoc, hy, hyy, mul_zero, zero_sub, sub_zero, neg_neg]

/-- The sum and difference of the two products commute, using square-zero. -/
theorem anticomm_mul_commutator (hx : X * X = 0) (hy : Y * Y = 0) :
    (X * Y + Y * X) * (X * Y - Y * X) =
      (X * Y - Y * X) * (X * Y + Y * X) := by
  have hxy : X * Y * (Y * X) = 0 := by
    calc
      _ = X * (Y * Y) * X := by simp only [mul_assoc]
      _ = 0 := by rw [hy, mul_zero, zero_mul]
  have hyx : Y * X * (X * Y) = 0 := by
    calc
      _ = Y * (X * X) * Y := by simp only [mul_assoc]
      _ = 0 := by rw [hx, mul_zero, zero_mul]
  simp only [mul_sub, add_mul, sub_mul, mul_add, hxy, hyx, add_zero, zero_add,
    sub_zero, zero_sub, sub_eq_add_neg]

/-- Only the product difference has the claimed negative sandwich image. -/
theorem sandwich_commutator (hx : X * X = 0) (hy : Y * Y = 0) :
    symmSandwich X Y (X * Y - Y * X) =
      -((X * Y + Y * X) * (X * Y - Y * X)) := by
  rw [symmSandwich_apply, commutator_anticomm_left hx, commutator_anticomm_right hy,
    anticomm_mul_commutator hx hy]
  noncomm_ring

theorem dissipator_anticomm (hx : X * X = 0) (hy : Y * Y = 0) :
    symmDissipator X Y (X * Y + Y * X) = 0 := by
  rw [symmDissipator_apply, sandwich_anticomm hx hy, two_smul]
  abel

theorem dissipator_add (hx : X * X = 0) (hy : Y * Y = 0) :
    symmDissipator X Y (X + Y) = -((2 : R) • ((X * Y + Y * X) * (X + Y))) := by
  rw [symmDissipator_apply, sandwich_add hx hy, smul_zero, zero_sub]
  congr 1
  rw [two_smul]
  simp only [mul_add, add_mul, ← anticomm_mul_left hx, ← anticomm_mul_right hy]

theorem dissipator_sub (hx : X * X = 0) (hy : Y * Y = 0) :
    symmDissipator X Y (X - Y) = -((2 : R) • ((X * Y + Y * X) * (X - Y))) := by
  rw [symmDissipator_apply, sandwich_sub hx hy, smul_zero, zero_sub]
  congr 1
  rw [two_smul]
  simp only [mul_sub, sub_mul, ← anticomm_mul_left hx, ← anticomm_mul_right hy]

theorem dissipator_commutator (hx : X * X = 0) (hy : Y * Y = 0) :
    symmDissipator X Y (X * Y - Y * X) =
      -((4 : R) • ((X * Y + Y * X) * (X * Y - Y * X))) := by
  rw [symmDissipator_apply, sandwich_commutator hx hy, ← anticomm_mul_commutator hx hy]
  module

/-- The complete corrected action on the sum, including the inner derivation. -/
theorem generator_add (hx : X * X = 0) (hy : Y * Y = 0) :
    symmGenerator X Y (X + Y) = -((2 : R) • ((X * Y + Y * X) * (X + Y))) := by
  rw [generator_eq_dissipator X Y (X + Y) (by
    simp only [mul_add, add_mul, anticomm_mul_left hx, anticomm_mul_right hy]),
    dissipator_add hx hy]

theorem generator_sub (hx : X * X = 0) (hy : Y * Y = 0) :
    symmGenerator X Y (X - Y) = -((2 : R) • ((X * Y + Y * X) * (X - Y))) := by
  rw [generator_eq_dissipator X Y (X - Y) (by
    simp only [mul_sub, sub_mul, anticomm_mul_left hx, anticomm_mul_right hy]),
    dissipator_sub hx hy]

theorem generator_anticomm (hx : X * X = 0) (hy : Y * Y = 0) :
    symmGenerator X Y (X * Y + Y * X) = 0 := by
  rw [generator_eq_dissipator X Y _ rfl, dissipator_anticomm hx hy]

theorem generator_commutator (hx : X * X = 0) (hy : Y * Y = 0) :
    symmGenerator X Y (X * Y - Y * X) =
      -((4 : R) • ((X * Y + Y * X) * (X * Y - Y * X))) := by
  rw [generator_eq_dissipator X Y _ (anticomm_mul_commutator hx hy),
    dissipator_commutator hx hy]

end InfoGeometry.Core.SquareZeroSandwich
