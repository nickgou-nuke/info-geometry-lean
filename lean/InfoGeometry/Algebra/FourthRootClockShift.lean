/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.Ext
import Mathlib.Tactic.NormNum

/-!
# Native four-state clock and shift

This focused owner contains the existing fourth-root phase and clock/shift
declarations, with their original namespace and proof bodies. The Fourier
projector constructions import this module. No projector interface or
repository graph infrastructure is needed for these finite matrix laws.
-/

noncomputable section

namespace InfoGeometry.Algebra.FourthRootPeirceProjectors

/-- The four scalar characters in the canonical order. -/
def phase (k : Fin 4) : ℂ := Complex.I ^ k.val

@[simp] theorem phase_fourth (k : Fin 4) : phase k ^ 4 = 1 := by
  fin_cases k <;> norm_num [phase, pow_succ, Complex.I_mul_I]

/-- Cyclic sector shifting does not by itself imply nilpotency. -/
def cyclicShift : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0,0,0,1; 1,0,0,0; 0,1,0,0; 0,0,1,0]

def degreeClock : Matrix (Fin 4) (Fin 4) ℂ := Matrix.diagonal phase

theorem cyclicShift_fourth : cyclicShift^4 = 1 := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [cyclicShift, pow_succ, Matrix.mul_apply, Fin.sum_univ_succ]

theorem degreeClock_fourth : degreeClock^4 = 1 := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [degreeClock, phase, Matrix.diagonal, pow_succ,
      Matrix.mul_apply, Fin.sum_univ_succ, Complex.I_mul_I]

/-- The clock-shift covariance holds although the shift has fourth power one. -/
theorem degreeClock_shift : degreeClock * cyclicShift =
    Complex.I • (cyclicShift * degreeClock) := by
  ext i j
  rw [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Matrix.mul_apply]
  fin_cases i <;> fin_cases j <;>
    norm_num [degreeClock, cyclicShift, phase, Matrix.diagonal,
      Fin.sum_univ_succ, pow_succ, Complex.I_mul_I]

theorem cyclicShift_fourth_ne_zero : cyclicShift^4 ≠ 0 := by
  rw [cyclicShift_fourth]
  exact one_ne_zero

/-- A concrete off-diagonal entry detects the noncommutative exchange. -/
theorem degreeClock_mul_shift_ne_shift_mul_clock :
    degreeClock * cyclicShift ≠ cyclicShift * degreeClock := by
  intro h
  have him := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => (M 1 0).im) h
  norm_num [degreeClock, cyclicShift, phase, Matrix.mul_apply,
    Fin.sum_univ_four] at him

end InfoGeometry.Algebra.FourthRootPeirceProjectors
