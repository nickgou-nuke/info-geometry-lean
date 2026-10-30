/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
module

public import Mathlib.Data.Matrix.Basis

/-! Noncommuting matrix units in every full finite matrix algebra with at least
 two indices, over any nontrivial ring. This makes the dimension hypothesis
 explicit; it does not assert noncommutativity for zero- or one-dimensional matrices. -/
public section

noncomputable section
namespace InfoGeometry.Algebra.FiniteMatrixNoncommutativity

section Generic

variable {n : ℕ} [Nontrivial (Fin n)]

private def firstIndex : Fin n := Classical.choose (exists_pair_ne (Fin n))
private def secondIndex : Fin n :=
  Classical.choose (Classical.choose_spec (exists_pair_ne (Fin n)))
private theorem indices_ne : (firstIndex : Fin n) ≠ secondIndex :=
  Classical.choose_spec (Classical.choose_spec (exists_pair_ne (Fin n)))

variable {R : Type*} [Ring R]

def forwardUnit : Matrix (Fin n) (Fin n) R :=
  Matrix.single firstIndex secondIndex 1

def backwardUnit : Matrix (Fin n) (Fin n) R :=
  Matrix.single secondIndex firstIndex 1

theorem forward_backward_ne [Nontrivial R] :
    (forwardUnit : Matrix (Fin n) (Fin n) R) * backwardUnit ≠
      backwardUnit * forwardUnit := by
  intro h
  have he := congrArg (fun M : Matrix (Fin n) (Fin n) R => M firstIndex firstIndex) h
  simp only [forwardUnit, backwardUnit] at he
  rw [Matrix.single_mul_single_same, Matrix.single_mul_single_same] at he
  simp [Matrix.single, Ne.symm indices_ne] at he

end Generic

variable {R : Type*} [Ring R]

def forward2 : Matrix (Fin 2) (Fin 2) R := forwardUnit

def backward2 : Matrix (Fin 2) (Fin 2) R := backwardUnit

theorem forward2_backward2_ne [Nontrivial R] :
    (forward2 : Matrix (Fin 2) (Fin 2) R) * backward2 ≠
      backward2 * forward2 := forward_backward_ne

def forward3 : Matrix (Fin 3) (Fin 3) R := forwardUnit

def backward3 : Matrix (Fin 3) (Fin 3) R := backwardUnit

theorem forward3_backward3_ne [Nontrivial R] :
    (forward3 : Matrix (Fin 3) (Fin 3) R) * backward3 ≠
      backward3 * forward3 := forward_backward_ne

section Four
variable {K : Type*} [Ring K]

def forward4 : Matrix (Fin 4) (Fin 4) K := forwardUnit

def backward4 : Matrix (Fin 4) (Fin 4) K := backwardUnit

theorem forward4_backward4_ne [Nontrivial K] :
    (forward4 : Matrix (Fin 4) (Fin 4) K) * backward4 ≠
      backward4 * forward4 := forward_backward_ne

end Four

def forward5 : Matrix (Fin 5) (Fin 5) R := forwardUnit

def backward5 : Matrix (Fin 5) (Fin 5) R := backwardUnit

theorem forward5_backward5_ne [Nontrivial R] :
    (forward5 : Matrix (Fin 5) (Fin 5) R) * backward5 ≠
      backward5 * forward5 := forward_backward_ne

end InfoGeometry.Algebra.FiniteMatrixNoncommutativity
