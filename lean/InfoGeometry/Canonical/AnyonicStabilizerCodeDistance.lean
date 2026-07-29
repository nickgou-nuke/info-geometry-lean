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

namespace AnyonicStabilizer

variable {n : ℕ} [Fintype (Fin n)] [DecidableEq (Fin n)]

/-- Anyonic Quantum Stabilizer Generator g with g * g† = 1. -/
structure AnyonStabilizerGenerator (n : ℕ) [Fintype (Fin n)] [DecidableEq (Fin n)] where
  g_val : Matrix (Fin n) (Fin n) ℂ
  g_dagger : Matrix (Fin n) (Fin n) ℂ
  h_unitary : g_val * g_dagger = 1
  h_unitary_rev : g_dagger * g_val = 1

namespace AnyonStabilizerGenerator

variable (g : AnyonStabilizerGenerator n)

/-- **Theorem**: Anyon Stabilizer Generator Unitarity g * g† = 1. -/
theorem anyon_stabilizer_unitary : g.g_val * g.g_dagger = 1 :=
  g.h_unitary

/-- Logical Operator L commuting with all stabilizer generators [g, L] = 0. -/
structure LogicalOperator (g : AnyonStabilizerGenerator n) where
  L_val : Matrix (Fin n) (Fin n) ℂ
  h_comm : g.g_val * L_val = L_val * g.g_val

namespace LogicalOperator

variable {g : AnyonStabilizerGenerator n} (L : LogicalOperator g)

/-- **Theorem**: Logical Operator Commutator Identity [g, L] = 0. -/
theorem logical_operator_commute : g.g_val * L.L_val - L.L_val * g.g_val = 0 := by
  have h := L.h_comm
  rw [h, sub_self]

/-- **Theorem**: Logical Operator Conjugation Invariance g * L * g† = L. -/
theorem logical_operator_conjugation_invariant :
    g.g_val * L.L_val * g.g_dagger = L.L_val := by
  calc g.g_val * L.L_val * g.g_dagger
    _ = L.L_val * g.g_val * g.g_dagger := by rw [L.h_comm]
    _ = L.L_val * (g.g_val * g.g_dagger) := by noncomm_ring
    _ = L.L_val * 1 := by rw [g.h_unitary]
    _ = L.L_val := by noncomm_ring

/-- **Theorem**: Logical Operator Trace Protection Invariance: Tr(g * L * g†) = Tr(L). -/
theorem logical_operator_trace_protected :
    trace (g.g_val * L.L_val * g.g_dagger) = trace L.L_val := by
  rw [L.logical_operator_conjugation_invariant]

end LogicalOperator

end AnyonStabilizerGenerator

end AnyonicStabilizer
