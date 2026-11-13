/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.IntervalCases

/-!
# Noncentral commutators of determinant-one orthogonal matrices

The first pair consists of the submitted block swap and quarter turn in
dimension four. Its multiplicative commutator has square `-1`, exact order
four, and fails to commute with the block swap.

The second pair consists of two signed transpositions. Both matrices are
orthogonal and have determinant one, but their multiplicative commutator has
exact order three. Thus orthogonality and determinant one do not imply that a
commutator's order divides the dimension. These are actual matrix products,
with transpose proved to be a two-sided inverse; they are not scalar
projective multipliers or spectral-gap witnesses.
-/

namespace InfoGeometry.Algebra.OrthogonalCommutatorExample

open Matrix

abbrev Mat4Z := Matrix (Fin 4) (Fin 4) ℤ

/-- Exchange the two coordinate planes. -/
def blockSwap : Mat4Z :=
  !![0, 0, 1, 0;
     0, 0, 0, 1;
     1, 0, 0, 0;
     0, 1, 0, 0]

/-- Rotate the first coordinate plane by a quarter turn. -/
def quarterTurn : Mat4Z :=
  !![0, -1, 0, 0;
     1,  0, 0, 0;
     0,  0, 1, 0;
     0,  0, 0, 1]

theorem blockSwap_transpose_mul : blockSwapᵀ * blockSwap = 1 := by decide

theorem blockSwap_mul_transpose : blockSwap * blockSwapᵀ = 1 := by decide

theorem quarterTurn_transpose_mul : quarterTurnᵀ * quarterTurn = 1 := by decide

theorem quarterTurn_mul_transpose : quarterTurn * quarterTurnᵀ = 1 := by decide

theorem blockSwap_det : blockSwap.det = 1 := by decide

theorem quarterTurn_det : quarterTurn.det = 1 := by decide

/-- The ordered product already retains the two distinct coordinate-plane actions. -/
theorem blockSwap_mul_quarterTurn :
    blockSwap * quarterTurn =
      !![0,  0, 1, 0;
         0,  0, 0, 1;
         0, -1, 0, 0;
         1,  0, 0, 0] := by decide

/-- The resulting full matrix-valued multiplicative commutator. -/
def commutatorMatrix : Mat4Z :=
  !![ 0, 1, 0,  0;
     -1, 0, 0,  0;
      0, 0, 0, -1;
      0, 0, 1,  0]

theorem blockSwap_quarterTurn_commutator :
    blockSwap * quarterTurn * blockSwapᵀ * quarterTurnᵀ = commutatorMatrix := by
  decide

theorem commutatorMatrix_transpose_mul : commutatorMatrixᵀ * commutatorMatrix = 1 := by
  decide

theorem commutatorMatrix_mul_transpose : commutatorMatrix * commutatorMatrixᵀ = 1 := by
  decide

theorem commutatorMatrix_det : commutatorMatrix.det = 1 := by decide

theorem commutatorMatrix_sq : commutatorMatrix ^ 2 = -1 := by decide

theorem commutatorMatrix_pow_four : commutatorMatrix ^ 4 = 1 := by decide

/-- Exact multiplicative order in the native matrix monoid. -/
theorem commutatorMatrix_orderOf : orderOf commutatorMatrix = 4 := by
  apply (orderOf_eq_iff (x := commutatorMatrix) (by decide : 0 < (4 : ℕ))).mpr
  refine ⟨commutatorMatrix_pow_four, ?_⟩
  intro m hm hpos
  interval_cases m <;> decide

/-- Conjugation by the block swap reverses the quarter-turn commutator. -/
theorem blockSwap_conjugate_commutator :
    blockSwap * commutatorMatrix * blockSwapᵀ = commutatorMatrixᵀ := by
  decide

/-- The concrete defect is noncentral, despite its finite order. -/
theorem commutatorMatrix_not_commute_blockSwap :
    commutatorMatrix * blockSwap ≠ blockSwap * commutatorMatrix := by
  decide

/-- Swap coordinates zero and one, and reverse coordinate three. -/
def signedSwap01 : Mat4Z :=
  !![0, 1, 0,  0;
     1, 0, 0,  0;
     0, 0, 1,  0;
     0, 0, 0, -1]

/-- Swap coordinates one and two, and reverse coordinate three. -/
def signedSwap12 : Mat4Z :=
  !![1, 0, 0,  0;
     0, 0, 1,  0;
     0, 1, 0,  0;
     0, 0, 0, -1]

theorem signedSwap01_transpose_mul : signedSwap01ᵀ * signedSwap01 = 1 := by decide

theorem signedSwap01_mul_transpose : signedSwap01 * signedSwap01ᵀ = 1 := by decide

theorem signedSwap12_transpose_mul : signedSwap12ᵀ * signedSwap12 = 1 := by decide

theorem signedSwap12_mul_transpose : signedSwap12 * signedSwap12ᵀ = 1 := by decide

theorem signedSwap01_det : signedSwap01.det = 1 := by decide

theorem signedSwap12_det : signedSwap12.det = 1 := by decide

/-- An order-three multiplicative commutator in dimension four. -/
def signedSwapCommutator : Mat4Z :=
  signedSwap01 * signedSwap12 * signedSwap01ᵀ * signedSwap12ᵀ

theorem signedSwapCommutator_eq :
    signedSwapCommutator =
      !![0, 1, 0, 0;
         0, 0, 1, 0;
         1, 0, 0, 0;
         0, 0, 0, 1] := by decide

theorem signedSwapCommutator_pow_three : signedSwapCommutator ^ 3 = 1 := by decide

theorem signedSwapCommutator_orderOf : orderOf signedSwapCommutator = 3 := by
  apply (orderOf_eq_iff (x := signedSwapCommutator) (by decide : 0 < (3 : ℕ))).mpr
  refine ⟨signedSwapCommutator_pow_three, ?_⟩
  intro m hm hpos
  interval_cases m <;> decide

/-- Finite order of an orthogonal commutator need not divide the dimension. -/
theorem signedSwapCommutator_order_not_dvd_dimension :
    ¬ orderOf signedSwapCommutator ∣ Fintype.card (Fin 4) := by
  rw [signedSwapCommutator_orderOf]
  decide

end InfoGeometry.Algebra.OrthogonalCommutatorExample
