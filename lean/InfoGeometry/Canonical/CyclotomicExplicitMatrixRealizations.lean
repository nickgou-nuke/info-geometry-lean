/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CyclotomicExplicitMatrixBridge

/-!
# Concrete cyclotomic matrix witnesses

These are finite representation-neutral witnesses.  They do not identify a
matrix with a physical Hamiltonian or a Lie-group action.
-/


namespace InfoGeometry.Canonical.CyclotomicExplicitMatrixRealizations

set_option maxRecDepth 100000

open Matrix

abbrev M3Z := InfoGeometry.Algebra.FiniteSpin.Mat3Z
abbrev M8Z := InfoGeometry.Algebra.FiniteSpin.Mat8Z

def tripotentStage : M3Z :=
  !![1, 0, 0; 0, -1, 0; 0, 0, 0]

theorem tripotentStage_cube : tripotentStage ^ 3 = tripotentStage := by
  decide

def phi24Companion : M8Z :=
  !![0, 0, 0, 0, 0, 0, 0, -1;
     1, 0, 0, 0, 0, 0, 0,  0;
     0, 1, 0, 0, 0, 0, 0,  0;
     0, 0, 1, 0, 0, 0, 0,  0;
     0, 0, 0, 1, 0, 0, 0,  1;
     0, 0, 0, 0, 1, 0, 0,  0;
     0, 0, 0, 0, 0, 1, 0,  0;
     0, 0, 0, 0, 0, 0, 1,  0]

theorem phi24Companion_polynomial :
    phi24Companion ^ 8 - phi24Companion ^ 4 + 1 = 0 := by
  decide

theorem phi24Companion_pow_twenty_four : phi24Companion ^ 24 = 1 := by
  change InfoGeometry.Canonical.CyclotomicExplicitMatrixBridge.phi24Companion ^ 24 = 1
  exact InfoGeometry.Canonical.CyclotomicExplicitMatrixBridge.phi24Companion_order

theorem phi24Companion_master25 : phi24Companion ^ 25 = phi24Companion := by
  rw [show (25 : ℕ) = 24 + 1 by norm_num, pow_add, pow_one,
    phi24Companion_pow_twenty_four]
  simp


abbrev M1Z := Matrix (Fin 1) (Fin 1) ℤ
abbrev M2Z := Matrix (Fin 2) (Fin 2) ℤ
abbrev M4Z := Matrix (Fin 4) (Fin 4) ℤ
abbrev M4Q := Matrix (Fin 4) (Fin 4) ℚ

def zeroStage : M1Z := 0
@[simp] theorem zeroStage_eq_zero : zeroStage = 0 := rfl

theorem tripotentStage_master25 : tripotentStage ^ 25 = tripotentStage := by
  decide

def complexStage : M3Z := !![0, -1, 0; 1, 0, 0; 0, 0, 0]
theorem complexStage_cube_neg : complexStage ^ 3 = -complexStage := by decide
theorem complexStage_master25 : complexStage ^ 25 = complexStage := by
  decide

def phi6Companion : M2Z := !![0, -1; 1, 1]
theorem phi6Companion_polynomial :
    phi6Companion ^ 2 - phi6Companion + 1 = 0 := by decide
theorem phi6Companion_pow_six : phi6Companion ^ 6 = 1 := by decide
theorem phi6Companion_master25 : phi6Companion ^ 25 = phi6Companion := by
  decide

def phi8Companion : M4Z :=
  !![0, 0, 0, -1; 1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0]
theorem phi8Companion_polynomial : phi8Companion ^ 4 + 1 = 0 := by decide
theorem phi8Companion_pow_four : phi8Companion ^ 4 = -1 := by decide
theorem phi8Companion_pow_eight : phi8Companion ^ 8 = 1 := by decide
theorem phi8Companion_master25 : phi8Companion ^ 25 = phi8Companion := by
  decide

def phi12Companion : M4Z :=
  !![0, 0, 0, -1; 1, 0, 0, 0; 0, 1, 0, 1; 0, 0, 1, 0]
theorem phi12Companion_polynomial :
    phi12Companion ^ 4 - phi12Companion ^ 2 + 1 = 0 := by decide
theorem phi12Companion_pow_twelve : phi12Companion ^ 12 = 1 := by decide
theorem phi12Companion_master25 : phi12Companion ^ 25 = phi12Companion := by
  decide

def hermitianRankOnePeirceOperator : M4Q :=
  !![1, 0, 0, 0; 0, 0, 0, 0; 0, 0, (1 / 2 : ℚ), 0; 0, 0, 0, (1 / 2 : ℚ)]
theorem hermitianRankOnePeirceOperator_not_tripotent :
    hermitianRankOnePeirceOperator ^ 3 ≠ hermitianRankOnePeirceOperator := by
  intro h
  have h22 := congrArg (fun M : M4Q => M 2 2) h
  norm_num [hermitianRankOnePeirceOperator, pow_three, Matrix.mul_apply, Fin.sum_univ_four] at h22
theorem hermitianRankOnePeirceOperator_not_master25 :
    hermitianRankOnePeirceOperator ^ 25 ≠ hermitianRankOnePeirceOperator := by
  intro h
  have h22 := congrArg (fun M : M4Q => M 2 2) h
  norm_num [hermitianRankOnePeirceOperator, pow_succ, Matrix.mul_apply, Fin.sum_univ_four] at h22

theorem explicit_cyclotomic_matrix_packet :
    tripotentStage ^ 3 = tripotentStage ∧
    complexStage ^ 3 = -complexStage ∧
    phi6Companion ^ 6 = 1 ∧
    phi8Companion ^ 4 = -1 ∧
    phi12Companion ^ 12 = 1 ∧
    phi24Companion ^ 24 = 1 := by
  exact ⟨tripotentStage_cube, complexStage_cube_neg, phi6Companion_pow_six,
    phi8Companion_pow_four, phi12Companion_pow_twelve,
    phi24Companion_pow_twenty_four⟩

end InfoGeometry.Canonical.CyclotomicExplicitMatrixRealizations
