import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
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
  R12 : Matrix.unitaryGroup (Fin n) ℂ
  R23 : Matrix.unitaryGroup (Fin n) ℂ
  h_yang_baxter :
    (R12 : Matrix (Fin n) (Fin n) ℂ) * R23 * R12 =
      (R23 : Matrix (Fin n) (Fin n) ℂ) * R12 * R23

namespace YangBaxterBraidingSystem

variable (sys : YangBaxterBraidingSystem n)

def R12Val : Matrix (Fin n) (Fin n) ℂ := sys.R12

def R23Val : Matrix (Fin n) (Fin n) ℂ := sys.R23

theorem h_R12_unitary : R12Val sys * (R12Val sys).conjTranspose = 1 := by
  change (sys.R12 : Matrix (Fin n) (Fin n) ℂ) *
      (sys.R12 : Matrix (Fin n) (Fin n) ℂ).conjTranspose = 1
  exact Matrix.mem_unitaryGroup_iff.mp sys.R12.2

theorem h_R23_unitary : R23Val sys * (R23Val sys).conjTranspose = 1 := by
  change (sys.R23 : Matrix (Fin n) (Fin n) ℂ) *
      (sys.R23 : Matrix (Fin n) (Fin n) ℂ).conjTranspose = 1
  exact Matrix.mem_unitaryGroup_iff.mp sys.R23.2

/-- **Theorem**: Yang-Baxter Braid Commutator Identity R₁₂ R₂₃ R₁₂ - R₂₃ R₁₂ R₂₃ = 0. -/
theorem yang_baxter_identity :
    R12Val sys * R23Val sys * R12Val sys -
        R23Val sys * R12Val sys * R23Val sys = 0 := by
  dsimp [R12Val, R23Val]
  rw [sys.h_yang_baxter, sub_self]

/-- **Theorem**: Anyon Braid Operator Trace Commutativity: Tr(R₁₂ R₂₃) = Tr(R₂₃ R₁₂). -/
theorem braid_trace_comm :
    trace (R12Val sys * R23Val sys) = trace (R23Val sys * R12Val sys) :=
  trace_mul_comm (R12Val sys) (R23Val sys)

/-- **Theorem**: Anyon Braid Conjugate Transpose Trace Identity: Tr(R₁₂ R₁₂†) = n. -/
theorem braid_unitary_trace (sys : YangBaxterBraidingSystem n) :
    trace (R12Val sys * (R12Val sys).conjTranspose) = (n : ℂ) := by
  rw [h_R12_unitary sys, trace_one, Fintype.card_fin]

end YangBaxterBraidingSystem

end AnyonYangBaxter
