/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import InfoGeometry.OperatorAlgebra.FiniteMatrixNoncommutativeWitness

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace InfoGeometry.QuantumContext.CausalPetz

open Matrix

variable {R : Type*} [CommRing R]

def blockIntertwiner (K L : R) : Matrix (Fin 2) (Fin 2) R :=
  !![K, 0;
     L, 0]

def blockCausalState (s : R) : Matrix (Fin 2) (Fin 2) R :=
  !![s, 0;
     0, 0]

def petzBlockReconstruct (K L s : R) : Matrix (Fin 2) (Fin 2) R :=
  blockIntertwiner K L * blockCausalState s * (blockIntertwiner K L)ᵀ

/-- The 2×2 matrix trace. -/
def trace2 (M : Matrix (Fin 2) (Fin 2) R) : R :=
  M 0 0 + M 1 1

/-! ### 1. Gram Partial Isometry Constraint -/

/-- The Gram operator Vᵀ · V. -/
theorem blockIntertwiner_gram (K L : R) :
    (blockIntertwiner K L)ᵀ * blockIntertwiner K L =
    !![K^2 + L^2, 0;
       0,         0] := by
  ext i j
  fin_cases i <;> fin_cases j
  · dsimp [blockIntertwiner]
    simp [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two]
    ring
  · dsimp [blockIntertwiner]
    simp [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two]
  · dsimp [blockIntertwiner]
    simp [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two]
  · dsimp [blockIntertwiner]
    simp [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two]

/-- The CPTP Stiefel condition: Vᵀ · V = P_supp ↔ K² + L² = 1. -/
theorem gram_isometry_iff_stiefel (K L : R) :
    (blockIntertwiner K L)ᵀ * blockIntertwiner K L = !![1, 0; 0, 0] ↔
    K^2 + L^2 = 1 := by
  rw [blockIntertwiner_gram]
  constructor
  · intro h
    have h00 := congr_fun (congr_fun h 0) 0
    exact h00
  · intro h
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h]

/-! ### 2. Trace Conservation Law -/

/-- 
Trace Preservation Theorem:
Under the Stiefel constraint K² + L² = 1, the total trace of the 
reconstructed density matrix strictly equals the input scalar s:
Tr(ℛ(σ)) = s.
-/
theorem petz_trace_preservation (K L s : R) (h_stiefel : K^2 + L^2 = 1) :
    trace2 (petzBlockReconstruct K L s) = s := by
  dsimp [trace2, petzBlockReconstruct, blockIntertwiner, blockCausalState]
  simp [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two]
  calc
    K * s * K + L * s * L = s * (K^2 + L^2) := by ring
    _ = s * 1 := by rw [h_stiefel]
    _ = s := mul_one s

/-- 
The Zero-Sum Generation Trade-Off:
If the past is perfectly preserved (K² = 1) in a trace-preserving channel, 
the future generation capacity is strictly ZERO (L² = 0).
-/
theorem past_preservation_forces_future_quiescence (K L : R)
    (h_stiefel : K^2 + L^2 = 1) (h_past : K^2 = 1) :
    L^2 = 0 := by
  calc
    L^2 = (K^2 + L^2) - K^2 := by ring
    _ = 1 - 1 := by rw [h_stiefel, h_past]
    _ = 0 := sub_self 1

/-- 
Future Dominance Forces Past Annihilation:
Conversely, if future generation is 100% (L² = 1), past prompt retention
is strictly ZERO (K² = 0), representing unconditioned generation / hallucination.
-/
theorem future_dominance_forces_past_annihilation (K L : R)
    (h_stiefel : K^2 + L^2 = 1) (h_future : L^2 = 1) :
    K^2 = 0 := by
  calc
    K^2 = (K^2 + L^2) - L^2 := by ring
    _ = 1 - 1 := by rw [h_stiefel, h_future]
    _ = 0 := sub_self 1

end InfoGeometry.QuantumContext.CausalPetz
