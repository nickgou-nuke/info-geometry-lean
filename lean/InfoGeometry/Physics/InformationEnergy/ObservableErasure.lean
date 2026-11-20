/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.InformationEnergy.TraceErasure
import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Observables of the full matrix trace-reset map

Trace duality identifies the backward observable of the existing reset map.
No matrices are assumed to commute, and no simultaneous diagonalization is
used. With a trace-one output matrix, the observables conserved against every
matrix input are exactly the scalar identities.

The final example has a mixed input, a pure output, and a positive nonscalar
Hamiltonian. All three relevant commutators are nonzero, yet this particular
input's energy expectation is unchanged by reset. This is an operator-algebra
statement; heat, entropy production, and a system-bath implementation are not
defined by the reset map alone.
-/

noncomputable section

namespace InfoGeometry.Physics.InformationEnergy.ObservableErasure

open Matrix

variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]

local notation "Mat" => Matrix n n K
local notation "E" => Matrix.traceLinearMap n K K

/-- The trace-dual observable of reset is the scalar identity with prepared expectation. -/
theorem trace_reset_pairing (σ X H : Mat) :
    Matrix.trace ((E).smulRight σ X * H) =
      Matrix.trace (X * (Matrix.trace (σ * H) • (1 : Mat))) := by
  change Matrix.trace ((Matrix.trace X • σ) * H) = _
  simp only [smul_mul_assoc, mul_smul_comm, Matrix.mul_one, Matrix.trace_smul, smul_eq_mul]
  ring

/-- Conservation for every matrix input is equivalent to a backward fixed observable. -/
theorem trace_reset_conserved_iff (σ H : Mat) :
    (∀ X : Mat, Matrix.trace ((E).smulRight σ X * H) = Matrix.trace (X * H)) ↔
      Matrix.trace (σ * H) • (1 : Mat) = H := by
  simp_rw [trace_reset_pairing]
  exact Matrix.ext_iff_trace_mul_left.symm

/-- A normalized reset conserves exactly the scalar observables on the full matrix algebra. -/
theorem trace_reset_conserved_iff_scalar (σ H : Mat) (hσ : Matrix.trace σ = 1) :
    (∀ X : Mat, Matrix.trace ((E).smulRight σ X * H) = Matrix.trace (X * H)) ↔
      ∃ c : K, H = c • (1 : Mat) := by
  rw [trace_reset_conserved_iff]
  constructor
  · intro h
    exact ⟨Matrix.trace (σ * H), h.symm⟩
  · rintro ⟨c, rfl⟩
    rw [mul_smul_comm, Matrix.mul_one, Matrix.trace_smul, hσ]
    simp

/-- A noncommuting positive mixed-to-pure state change can preserve one
Hamiltonian expectation. Universal observable conservation is a stronger
condition, characterized above. The output here is a trace-one positive
rank-one matrix; no entropy or heat assertion is part of this example. -/
theorem noncommuting_reset_equal_energy :
    ∃ H ρ σ : Matrix (Fin 2) (Fin 2) ℝ,
      H.PosSemidef ∧ ρ.PosSemidef ∧ σ.PosSemidef ∧
      Matrix.trace ρ = 1 ∧ Matrix.trace σ = 1 ∧
      ρ * ρ ≠ ρ ∧ σ * σ = σ ∧
      ρ * σ ≠ σ * ρ ∧ H * ρ ≠ ρ * H ∧ H * σ ≠ σ * H ∧
      (Matrix.traceLinearMap (Fin 2) ℝ ℝ).smulRight σ ρ = σ ∧
      Matrix.trace ((Matrix.traceLinearMap (Fin 2) ℝ ℝ).smulRight σ ρ * H) =
        Matrix.trace (ρ * H) := by
  let H : Matrix (Fin 2) (Fin 2) ℝ := !![5, 1; 1, 1]
  let ρ : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![3 / 4, 1 / 4]
  let σ : Matrix (Fin 2) (Fin 2) ℝ := !![1 / 2, 1 / 2; 1 / 2, 1 / 2]
  let A : Matrix (Fin 2) (Fin 2) ℝ := !![2, 0; 1, 1]
  let B : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 0, 0]
  have hHgram : Aᴴ * A = H := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A, H, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two]
  have hσgram : (1 / 2 : ℝ) • (Bᴴ * B) = σ := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [B, σ, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two]
  have hH : H.PosSemidef := by
    rw [← hHgram]
    exact Matrix.posSemidef_conjTranspose_mul_self A
  have hρ : ρ.PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    fin_cases i <;> norm_num
  have hσ : σ.PosSemidef := by
    rw [← hσgram]
    exact (Matrix.posSemidef_conjTranspose_mul_self B).smul (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have htrρ : Matrix.trace ρ = 1 := by
    norm_num [ρ, Matrix.trace, Fin.sum_univ_two]
  have htrσ : Matrix.trace σ = 1 := by
    norm_num [σ, Matrix.trace, Fin.sum_univ_two]
  have hreset : (Matrix.traceLinearMap (Fin 2) ℝ ℝ).smulRight σ ρ = σ := by
    change Matrix.trace ρ • σ = σ
    rw [htrρ, one_smul]
  refine ⟨H, ρ, σ, hH, hρ, hσ, htrρ, htrσ, ?_, ?_, ?_, ?_, ?_, hreset, ?_⟩
  · intro h
    have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h
    norm_num [ρ, Matrix.mul_apply, Fin.sum_univ_two] at he
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [σ, Matrix.mul_apply, Fin.sum_univ_two]
  · intro h
    have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) h
    norm_num [ρ, σ, Matrix.mul_apply, Fin.sum_univ_two] at he
  · intro h
    have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) h
    norm_num [H, ρ, Matrix.mul_apply, Fin.sum_univ_two] at he
  · intro h
    have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) h
    norm_num [H, σ, Matrix.mul_apply, Fin.sum_univ_two] at he
  · rw [hreset]
    norm_num [H, ρ, σ, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two]

/-- Positive trace-one states themselves need not commute. The displayed
pair consists of the mixed input and pure output of the proved reset example. -/
theorem positive_trace_one_noncommuting_pair :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℝ,
      A * B ≠ B * A ∧ A.PosSemidef ∧ B.PosSemidef ∧
      Matrix.trace A = 1 ∧ Matrix.trace B = 1 ∧ A * A ≠ A ∧ B * B = B := by
  obtain ⟨_, A, B, _, hA, hB, htrA, htrB, hmixed, hpure, hAB, _⟩ :=
    noncommuting_reset_equal_energy
  exact ⟨A, B, hAB, hA, hB, htrA, htrB, hmixed, hpure⟩

end InfoGeometry.Physics.InformationEnergy.ObservableErasure
