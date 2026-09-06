import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NoncommRing

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.dupNamespace false

noncomputable section

open Matrix Complex

namespace QuantumDoubleS3Bridge

/-- Simple Anyons in the Non-Abelian Quantum Double D(S₃):
- A1, A2, A3 : Flux A = {e}         (Pure Electric Sector)
- B1, B2     : Flux B = {(12), ...} (Transposition Flux Sector)
- C1, C2, C3 : Flux C = {(123), ..} (3-Cycle Flux Sector) -/
inductive S3Anyon : Type
  | A1 : S3Anyon
  | A2 : S3Anyon
  | A3 : S3Anyon
  | B1 : S3Anyon
  | B2 : S3Anyon
  | C1 : S3Anyon
  | C2 : S3Anyon
  | C3 : S3Anyon
  deriving DecidableEq

instance : Fintype S3Anyon where
  elems := {S3Anyon.A1, S3Anyon.A2, S3Anyon.A3, S3Anyon.B1, S3Anyon.B2, S3Anyon.C1, S3Anyon.C2, S3Anyon.C3}
  complete := by rintro (_ | _ | _ | _ | _ | _ | _ | _) <;> decide

open S3Anyon

/-- Order of the permutation group S₃: |S₃| = 6. -/
def groupOrderS3 : ℝ := 6

/-- Quantum Dimensions d_i = |C_i| · dim(χ_i). -/
def quantumDim : S3Anyon → ℝ
  | A1 => 1
  | A2 => 1
  | A3 => 2
  | B1 => 3
  | B2 => 3
  | C1 => 2
  | C2 => 2
  | C3 => 2

/-- **Theorem**: Individual Quantum Dimensions Match Formula d_i ∈ {1, 2, 3}. -/
theorem quantumDim_values (a : S3Anyon) :
    quantumDim a = 1 ∨ quantumDim a = 2 ∨ quantumDim a = 3 := by
  cases a <;> { first | left; rfl | right; left; rfl | right; right; rfl }

/-- **Theorem**: Sum of Squared Quantum Dimensions Equals |S₃|² = 36. -/
theorem sum_quantum_dim_sq_eq_thirty_six :
    (quantumDim A1)^2 + (quantumDim A2)^2 + (quantumDim A3)^2 +
    (quantumDim B1)^2 + (quantumDim B2)^2 +
    (quantumDim C1)^2 + (quantumDim C2)^2 + (quantumDim C3)^2 = 36 := by
  dsimp [quantumDim]
  ring

/-- **Theorem**: Total Quantum Dimension 𝒯 = |S₃| = 6. -/
theorem total_quantum_dim_s3 :
    Real.sqrt ((quantumDim A1)^2 + (quantumDim A2)^2 + (quantumDim A3)^2 +
               (quantumDim B1)^2 + (quantumDim B2)^2 +
               (quantumDim C1)^2 + (quantumDim C2)^2 + (quantumDim C3)^2) = groupOrderS3 := by
  rw [sum_quantum_dim_sq_eq_thirty_six]
  dsimp [groupOrderS3]
  have h36 : (36 : ℝ) = (6 : ℝ) ^ 2 := by norm_num
  rw [h36]
  exact Real.sqrt_sq (by norm_num)

end QuantumDoubleS3Bridge
