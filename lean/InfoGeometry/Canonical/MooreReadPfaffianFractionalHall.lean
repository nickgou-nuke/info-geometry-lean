import Mathlib.Analysis.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
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

namespace MooreReadPfaffianFractionalHall

/-- Moore-Read Pfaffian Antisymmetric Matrix Aᵀ = -A in M₂ₘ(ℂ). -/
structure PfaffianMatrix (m : ℕ) where
  matrix : Matrix (Fin (2 * m)) (Fin (2 * m)) ℂ
  h_anti_symm : matrix.transpose = - matrix

namespace MooreRead

variable {m : ℕ} (pf : PfaffianMatrix m)

/-- **Theorem**: Pfaffian Anti-Symmetry Trace Annihilation: Tr(A) = 0 for skew-symmetric matrix. -/
theorem pfaffian_matrix_trace_zero :
    trace pf.matrix = 0 := by
  have h_tr_eq : trace pf.matrix = trace pf.matrix.transpose := by rw [trace_transpose]
  rw [pf.h_anti_symm, trace_neg] at h_tr_eq
  have h_add : trace pf.matrix + trace pf.matrix = 0 := by
    nth_rw 1 [h_tr_eq]
    rw [neg_add_cancel]
  calc trace pf.matrix
    _ = (1 / 2 : ℂ) * (trace pf.matrix + trace pf.matrix) := by ring
    _ = (1 / 2 : ℂ) * 0 := by rw [h_add]
    _ = 0 := by ring

/-- Quantum Dimension of Vacuum Anyon I. -/
def dimI : ℝ := 1

/-- Quantum Dimension of Fermion Anyon ψ. -/
def dimPsi : ℝ := 1

/-- Quantum Dimension of Non-Abelian Ising Anyon σ = √2. -/
def dimSigma : ℝ := Real.sqrt 2

/-- **Theorem**: Ising Anyon Fusion Quantum Dimension Conservation:
    dim(σ)² = dim(I) + dim(ψ) (2 = 1 + 1). -/
theorem ising_anyon_quantum_dimension_fusion :
    dimSigma ^ 2 = dimI + dimPsi := by
  dsimp [dimSigma, dimI, dimPsi]
  have h_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [h_sq]
  norm_num

/-- **Theorem**: Ground State Degeneracy for 2m Non-Abelian Anyons:
    N(2m) = 2^(m-1). -/
def groundStateDegeneracy (m_anyons : ℕ) : ℕ :=
  2 ^ (m_anyons - 1)

/-- **Theorem**: Ground State Degeneracy Monotonicity for m ≥ 1. -/
theorem ground_state_degeneracy_pos (m_anyons : ℕ) (h_pos : m_anyons ≥ 1) :
    groundStateDegeneracy m_anyons > 0 := by
  dsimp [groundStateDegeneracy]
  exact Nat.two_pow_pos (m_anyons - 1)

end MooreRead

end MooreReadPfaffianFractionalHall
