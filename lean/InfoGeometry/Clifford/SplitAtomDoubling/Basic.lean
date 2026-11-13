/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

/-!
# Noncommutative block doubling

The original ring-valued definitions and proofs of `SplitAtomDoubling`, isolated
from the real Clifford classification imports. The old owner imports this file
and preserves every declaration name. The convention is
`negative = !![0, 1; -1, 0]`, opposite to the intake's negative-square generator.
-/

namespace InfoGeometry.Clifford.SplitAtomDoubling

section Blocks

variable {A : Type*} [Ring A]

abbrev Block2 (A : Type*) := Matrix (Fin 2) (Fin 2) A

def repeated (a : A) : Block2 A := !![a, 0; 0, a]

def twisted (a : A) : Block2 A := !![a, 0; 0, -a]

def positive : Block2 A := !![0, 1; 1, 0]

def negative : Block2 A := !![0, 1; -1, 0]

def repeatedHom : A →+* Block2 A where
  toFun := repeated
  map_one' := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [repeated]
  map_zero' := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [repeated]
  map_add' a b := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [repeated]
  map_mul' a b := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [repeated, Matrix.mul_apply, Fin.sum_univ_two]

theorem twisted_injective : Function.Injective (twisted (A := A)) := by
  intro a b h
  exact congrArg (fun M : Block2 A => M 0 0) h

theorem twisted_mul (a b : A) : twisted a * twisted b = repeated (a * b) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [twisted, repeated, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem positive_square : (positive : Block2 A) * positive = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [positive, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem negative_square : (negative : Block2 A) * negative = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [negative, Matrix.mul_apply, Fin.sum_univ_two]

theorem head_anticommutator :
    (positive : Block2 A) * negative + negative * positive = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [positive, negative]

theorem twisted_positive_anticommutator (a : A) :
    twisted a * positive + positive * twisted a = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [twisted, positive]

theorem twisted_negative_anticommutator (a : A) :
    twisted a * negative + negative * twisted a = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [twisted, negative]

/-- The old Clifford anticommutator is retained on the repeated diagonal. -/
theorem twisted_anticommutator (a b : A) :
    twisted a * twisted b + twisted b * twisted a = repeated (a * b + b * a) := by
  rw [twisted_mul, twisted_mul]
  exact (repeatedHom.map_add _ _).symm

end Blocks

end InfoGeometry.Clifford.SplitAtomDoubling
