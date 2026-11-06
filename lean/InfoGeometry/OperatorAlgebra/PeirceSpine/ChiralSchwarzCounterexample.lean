/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# A noncommuting matrix obstruction to collapse from wing tests

The carrier is the full rational matrix ring `Matrix (Fin 3) (Fin 3) ℚ`.
For the idempotent `cut = diag(1,0,1)` and `seed = E₀₁ + E₁₂`, the
existing Peirce corners are `upper = E₀₁` and `lower = E₁₂`. Their ordered
products differ: `upper * lower = E₀₂`, while `lower * upper = 0`.

Both commutators of `Σ` with the individual wings vanish, although
`V = Σ = E₀₂` is nonzero. Thus vanishing of those two tested values does
not force the interaction to vanish. This example does not make `Σ`
central in the full matrix ring; a separate theorem exhibits a detecting
input outside the two wings.

The same full matrix model distinguishes the ordered square linearization
`Φ * H + H * Φ` from `2 • (Φ * H)` at `H = cut`. This is an algebraic
linearization statement, with no claim of a logarithmic derivative,
positive metric, relative entropy, or analytic geometry.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine.ChiralSchwarzCounterexample

abbrev Op := Matrix (Fin 3) (Fin 3) ℚ

def cut : Op := !![1, 0, 0; 0, 0, 0; 0, 0, 1]
def seed : Op := !![0, 1, 0; 0, 0, 1; 0, 0, 0]
def upper : Op := !![0, 1, 0; 0, 0, 0; 0, 0, 0]
def lower : Op := !![0, 0, 0; 0, 0, 1; 0, 0, 0]
def residue : Op := !![0, 0, 1; 0, 0, 0; 0, 0, 0]
def reverseResidue : Op := !![0, 0, 0; 0, 0, 0; 1, 0, 0]

theorem cut_idempotent : cut * cut = cut := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [cut, Matrix.mul_apply, Fin.sum_univ_succ]

theorem conePlus_seed : conePlus cut seed = upper := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [conePlus, cut, seed, upper, Matrix.mul_apply,
      Matrix.vecMul_apply_eq_sum, Matrix.one_apply, Fin.sum_univ_succ]

theorem coneMinus_seed : coneMinus cut seed = lower := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [coneMinus, cut, seed, lower, Matrix.mul_apply,
      Matrix.vecMul_apply_eq_sum, Matrix.one_apply, Fin.sum_univ_succ]

theorem upper_mul_lower : upper * lower = residue := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [upper, lower, residue, Matrix.mul_apply, Fin.sum_univ_succ]

theorem lower_mul_upper : lower * upper = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [upper, lower, Matrix.mul_apply, Fin.sum_univ_succ]

theorem residue_ne_zero : residue ≠ 0 := by
  intro h
  have h02 := congrArg (fun M : Op => M 0 2) h
  norm_num [residue] at h02

theorem wings_noncommute : upper * lower ≠ lower * upper := by
  rw [upper_mul_lower, lower_mul_upper]
  exact residue_ne_zero

theorem interaction_value : genV cut seed seed = residue := by
  simp only [genV, anticomm, conePlus_seed, coneMinus_seed,
    upper_mul_lower, lower_mul_upper, add_zero]

theorem obstruction_value : genSig cut seed seed = residue := by
  simp only [genSig, comm, conePlus_seed, coneMinus_seed,
    upper_mul_lower, lower_mul_upper, sub_zero]

theorem interaction_ne_zero : genV cut seed seed ≠ 0 := by
  rw [interaction_value]
  exact residue_ne_zero

theorem obstruction_comm_upper : comm (genSig cut seed seed) upper = 0 := by
  rw [obstruction_value]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [comm, residue, upper, Matrix.mul_apply, Fin.sum_univ_succ]

theorem obstruction_comm_lower : comm (genSig cut seed seed) lower = 0 := by
  rw [obstruction_value]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [comm, residue, lower, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The two wing tests in the submitted collapse argument are insufficient. -/
theorem zero_wing_tests_with_nonzero_interaction :
    cut * cut = cut ∧
      comm (genSig cut seed seed) (conePlus cut seed) = 0 ∧
      comm (genSig cut seed seed) (coneMinus cut seed) = 0 ∧
      genV cut seed seed ≠ 0 := by
  exact ⟨cut_idempotent, by rw [conePlus_seed]; exact obstruction_comm_upper,
    by rw [coneMinus_seed]; exact obstruction_comm_lower, interaction_ne_zero⟩

/-- The nonzero interaction is square-zero; square-zero does not mean zero. -/
theorem interaction_square_zero :
    genV cut seed seed * genV cut seed seed = 0 := by
  rw [interaction_value]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [residue, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The obstruction is not central on the full matrix algebra. -/
theorem obstruction_detected_outside_wings :
    comm (genSig cut seed seed) reverseResidue ≠ 0 := by
  rw [obstruction_value]
  intro h
  have h00 := congrArg (fun M : Op => M 0 0) h
  norm_num [comm, residue, reverseResidue, Matrix.mul_apply,
    Fin.sum_univ_succ] at h00

theorem phi_mul_cut : genPhi cut seed seed * cut = lower := by
  rw [genPhi, add_mul, conePlus_mul_P cut_idempotent,
    coneMinus_mul_P cut_idempotent, zero_add, coneMinus_seed]

theorem cut_mul_phi : cut * genPhi cut seed seed = upper := by
  rw [genPhi, mul_add, P_mul_conePlus cut_idempotent,
    P_mul_coneMinus cut_idempotent, add_zero, conePlus_seed]

/-- The correct linear term of the square map at `Φ`, evaluated on `cut`. -/
theorem ordered_square_linearization :
    genPhi cut seed seed * cut + cut * genPhi cut seed seed =
      genPhi cut seed seed := by
  rw [phi_mul_cut, cut_mul_phi, genPhi, conePlus_seed, coneMinus_seed, add_comm]

theorem doubled_right_product_ne_phi :
    (2 : ℕ) • (genPhi cut seed seed * cut) ≠ genPhi cut seed seed := by
  rw [phi_mul_cut, genPhi, conePlus_seed, coneMinus_seed]
  intro h
  have h01 := congrArg (fun M : Op => M 0 1) h
  norm_num [upper, lower, Matrix.smul_apply] at h01

/-- Dropping the multiplication order changes the linearization. -/
theorem square_linearization_ne_doubled_product :
    genPhi cut seed seed * cut + cut * genPhi cut seed seed ≠
      (2 : ℕ) • (genPhi cut seed seed * cut) := by
  rw [ordered_square_linearization]
  exact doubled_right_product_ne_phi.symm

end InfoGeometry.OperatorAlgebra.PeirceSpine.ChiralSchwarzCounterexample
