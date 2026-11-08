/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PartnerGeneralizedEigenspaces
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Noncommuting three-dimensional operators with a genuine Jordan chain of length three. -/

namespace InfoGeometry.OperatorAlgebra.PartnerGeneralizedEigenspacesTests

open PartnerEigenspaces

noncomputable section

abbrev Carrier := Fin 3 → ℝ

def cycleMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, 1, 0; 0, 0, 1; 1, 0, 0]

def couplingMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, 0, 1; 1, 1, 0; 0, 1, 0]

def cycle : Module.End ℝ Carrier := Matrix.mulVecLin cycleMatrix

def coupling : Module.End ℝ Carrier := Matrix.mulVecLin couplingMatrix

def sourceVector : Carrier := ![0, 0, 1]

def targetVector : Carrier := ![0, 1, 0]

theorem cycle_apply (x : Carrier) : cycle x = ![x 1, x 2, x 0] := by
  ext i
  fin_cases i <;> simp [cycle, cycleMatrix,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem coupling_apply (x : Carrier) : coupling x = ![x 0 + x 2, x 0 + x 1, x 1] := by
  ext i
  fin_cases i <;> simp [coupling, couplingMatrix,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem sourceShift_apply (x : Carrier) :
    (coupling * cycle - 1) x = ![x 1, x 2, 0] := by
  ext i
  fin_cases i <;>
    simp [LinearMap.sub_apply, Module.End.mul_apply, cycle_apply, coupling_apply]

theorem targetShift_apply (x : Carrier) :
    (cycle * coupling - 1) x = ![x 1, 0, x 0] := by
  ext i
  fin_cases i <;>
    simp [LinearMap.sub_apply, Module.End.mul_apply, cycle_apply, coupling_apply]

theorem partner_matrices_do_not_commute :
    cycleMatrix * couplingMatrix ≠ couplingMatrix * cycleMatrix := by
  intro h
  have hentry := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 2 0) h
  norm_num [cycleMatrix, couplingMatrix, Matrix.mul_apply, Fin.sum_univ_succ] at hentry

theorem partner_operators_do_not_commute : cycle * coupling ≠ coupling * cycle := by
  intro h
  have hentry := congrArg (fun T : Module.End ℝ Carrier => T (![1, 0, 0]) 2) h
  norm_num [Module.End.mul_apply, cycle_apply, coupling_apply] at hentry

theorem source_exact_depth_three :
    sourceVector ∈ Module.End.genEigenspace (coupling * cycle) 1 3 ∧
      sourceVector ∉ Module.End.genEigenspace (coupling * cycle) 1 2 := by
  constructor
  · rw [show (3 : ℕ∞) = (3 : ℕ) by rfl, Module.End.mem_genEigenspace_nat,
      LinearMap.mem_ker]
    simp [pow_succ', Module.End.mul_apply, cycle_apply, coupling_apply, sourceVector]
  · intro h
    rw [show (2 : ℕ∞) = (2 : ℕ) by rfl, Module.End.mem_genEigenspace_nat,
      LinearMap.mem_ker] at h
    have hentry := congrArg (fun x : Carrier => x 0) h
    norm_num [pow_succ', Module.End.mul_apply, cycle_apply, coupling_apply, sourceVector] at hentry

theorem target_exact_depth_three :
    targetVector ∈ Module.End.genEigenspace (cycle * coupling) 1 3 ∧
      targetVector ∉ Module.End.genEigenspace (cycle * coupling) 1 2 := by
  constructor
  · rw [show (3 : ℕ∞) = (3 : ℕ) by rfl, Module.End.mem_genEigenspace_nat,
      LinearMap.mem_ker]
    simp [pow_succ', Module.End.mul_apply, cycle_apply, coupling_apply, targetVector]
  · intro h
    rw [show (2 : ℕ∞) = (2 : ℕ) by rfl, Module.End.mem_genEigenspace_nat,
      LinearMap.mem_ker] at h
    have hentry := congrArg (fun x : Carrier => x 2) h
    norm_num [pow_succ', Module.End.mul_apply, cycle_apply, coupling_apply, targetVector] at hentry

theorem equivalence_transports_exact_jordan_chain :
    (nonzeroGenEigenspaceEquiv cycle coupling 1 one_ne_zero 3
      ⟨sourceVector, source_exact_depth_three.1⟩ : Carrier) = targetVector := by
  rw [nonzeroGenEigenspaceEquiv_apply, cycle_apply]
  rfl

end

end InfoGeometry.OperatorAlgebra.PartnerGeneralizedEigenspacesTests
