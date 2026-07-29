import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NoncommRing

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

noncomputable section

open Matrix Complex

namespace AnyonYangBaxter

variable {n : ℕ} [DecidableEq (Fin n)]

/-- Anyonic Quantum Braiding R-Matrix System satisfying Yang-Baxter Equation R₁₂ R₂₃ R₁₂ = R₂₃ R₁₂ R₂₃. -/
structure YangBaxterBraidingSystem (n : ℕ) [DecidableEq (Fin n)] where
  R12 : Matrix (Fin n) (Fin n) ℂ
  R23 : Matrix (Fin n) (Fin n) ℂ
  h_yang_baxter : R12 * R23 * R12 = R23 * R12 * R23
  h_R12_unitary : R12 * R12.conjTranspose = 1
  h_R23_unitary : R23 * R23.conjTranspose = 1

namespace YangBaxterBraidingSystem

variable (sys : YangBaxterBraidingSystem n)

/-- **Theorem**: Yang-Baxter Braid Commutator Identity R₁₂ R₂₃ R₁₂ - R₂₃ R₁₂ R₂₃ = 0. -/
theorem yang_baxter_identity :
    sys.R12 * sys.R23 * sys.R12 - sys.R23 * sys.R12 * sys.R23 = 0 := by
  rw [sys.h_yang_baxter, sub_self]

/-- **Theorem**: Anyon Braid Operator Trace Commutativity: Tr(R₁₂ R₂₃) = Tr(R₂₃ R₁₂). -/
theorem braid_trace_comm :
    trace (sys.R12 * sys.R23) = trace (sys.R23 * sys.R12) :=
  trace_mul_comm sys.R12 sys.R23

/-- **Theorem**: Anyon Braid Conjugate Transpose Trace Identity: Tr(R₁₂ R₁₂†) = n. -/
theorem braid_unitary_trace (sys : YangBaxterBraidingSystem n) :
    trace (sys.R12 * sys.R12.conjTranspose) = (n : ℂ) := by
  rw [sys.h_R12_unitary, trace_one, Fintype.card_fin]

end YangBaxterBraidingSystem

end AnyonYangBaxter
