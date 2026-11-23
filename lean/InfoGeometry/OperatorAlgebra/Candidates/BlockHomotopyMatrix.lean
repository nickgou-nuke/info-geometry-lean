/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-!
# Degree-zero to degree-one block homotopy in a noncommutative matrix algebra

This is the algebraic block calculation behind a two-term contracting homotopy.
The coefficient ring is allowed to be noncommutative; multiplication order is
kept explicit. The hypotheses are the left-inverse identity `h * d = 1 - P`
and the vacuum-annihilation identity `d * P = 0`.

This result constructs no Hilbert space, bounded operator, norm estimate, or
spectral gap. Those analytic conclusions require the corresponding operator
representations and bounds.
-/

namespace InfoGeometry.OperatorAlgebra.Candidates.BlockHomotopyMatrix

open scoped Matrix

variable {A : Type*} [Ring A]

/-- The two off-diagonal matrix units. -/
def matrixUnit01 : Matrix (Fin 2) (Fin 2) A := !![0, 1; 0, 0]

def matrixUnit10 : Matrix (Fin 2) (Fin 2) A := !![0, 0; 1, 0]

/-- The two standard matrix units in a nontrivial coefficient ring do not
commute. This is a concrete witness in the actual matrix operator algebra. -/
theorem matrix_units_do_not_commute [Nontrivial A] :
    matrixUnit01 (A := A) * matrixUnit10 (A := A) ≠
      matrixUnit10 (A := A) * matrixUnit01 (A := A) := by
  intro h
  have hentry := congrArg (fun M : Matrix (Fin 2) (Fin 2) A => M 0 0) h
  have h10 : (1 : A) ≠ 0 := one_ne_zero
  apply h10
  simpa [matrixUnit01, matrixUnit10, Matrix.mul_apply,
    Fin.sum_univ_two] using hentry

/-- The differential from degree zero to degree one, in the ordered basis
`degree 0, degree 1`. -/
def differentialBlock (d : A) : Matrix (Fin 2) (Fin 2) A := !![0, 0; d, 0]

/-- A degree-lowering homotopy block. -/
def homotopyBlock (h : A) : Matrix (Fin 2) (Fin 2) A := !![0, h; 0, 0]

/-- The total projection: vacuum in degree zero and the complementary range
projection in degree one. -/
def totalProjection (P d h : A) : Matrix (Fin 2) (Fin 2) A :=
  !![P, 0; 0, 1 - d * h]

/-- The identity operator on the two-term block carrier. -/
def blockIdentity : Matrix (Fin 2) (Fin 2) A := !![1, 0; 0, 1]

theorem block_homotopy_identities (d h P : A)
    (hP : P * P = P)
    (hdP : d * P = 0)
    (hhd : h * d = 1 - P) :
    differentialBlock d * differentialBlock d = 0 ∧
    totalProjection P d h * totalProjection P d h = totalProjection P d h ∧
    differentialBlock d * totalProjection P d h = 0 ∧
    totalProjection P d h * differentialBlock d = 0 ∧
    differentialBlock d * homotopyBlock h + homotopyBlock h * differentialBlock d =
      blockIdentity - totalProjection P d h := by
  have hdh : (d * h) * (d * h) = d * h := by
    calc
      (d * h) * (d * h) = d * (h * d) * h := by simp only [mul_assoc]
      _ = d * (1 - P) * h := by rw [hhd]
      _ = d * h - (d * P) * h := by simp only [mul_sub, mul_one, sub_mul]
      _ = d * h := by rw [hdP, zero_mul, sub_zero]
  have hcomp : (1 - d * h) * d = 0 := by
    calc
      (1 - d * h) * d = d - d * (h * d) := by simp only [sub_mul, one_mul, mul_assoc]
      _ = d - d * (1 - P) := by rw [hhd]
      _ = d * P := by simp only [mul_sub, mul_one]; abel
      _ = 0 := hdP
  have hcomp_idem : (1 - d * h) * (1 - d * h) = 1 - d * h := by
    simp only [sub_mul, mul_sub, one_mul, mul_one]
    rw [hdh]
    abel
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [differentialBlock, Matrix.mul_apply, Fin.sum_univ_two]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [totalProjection, Matrix.mul_apply, Fin.sum_univ_two, hP, hcomp_idem]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [differentialBlock, totalProjection, Matrix.mul_apply,
        Fin.sum_univ_two, hdP]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [differentialBlock, totalProjection, Matrix.mul_apply,
        Fin.sum_univ_two, hcomp]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [differentialBlock, homotopyBlock, totalProjection, blockIdentity,
        hhd]

end InfoGeometry.OperatorAlgebra.Candidates.BlockHomotopyMatrix
