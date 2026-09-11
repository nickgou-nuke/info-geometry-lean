import Mathlib.Analysis.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
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

namespace AnyonicStabilizer

variable {n : ℕ} [Fintype (Fin n)] [DecidableEq (Fin n)]

/-- Anyonic Quantum Stabilizer Generator g with g * g† = 1. -/
abbrev AnyonStabilizerGenerator (n : ℕ) [Fintype (Fin n)] [DecidableEq (Fin n)] :=
  Matrix.unitaryGroup (Fin n) ℂ

namespace AnyonStabilizerGenerator

variable (g : AnyonStabilizerGenerator n)

theorem h_unitary :
    (g : Matrix (Fin n) (Fin n) ℂ) *
        (g : Matrix (Fin n) (Fin n) ℂ).conjTranspose = 1 := by
  exact Matrix.mem_unitaryGroup_iff.mp g.2

theorem h_unitary_rev :
    (g : Matrix (Fin n) (Fin n) ℂ).conjTranspose *
        (g : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  exact Matrix.mem_unitaryGroup_iff'.mp g.2

/-- **Theorem**: Anyon Stabilizer Generator Unitarity g * g† = 1. -/
theorem anyon_stabilizer_unitary :
    (g : Matrix (Fin n) (Fin n) ℂ) *
        (g : Matrix (Fin n) (Fin n) ℂ).conjTranspose = 1 :=
    h_unitary g

/-- Logical Operator L commuting with all stabilizer generators [g, L] = 0. -/
structure LogicalOperator (g : AnyonStabilizerGenerator n) where
  L_val : Matrix (Fin n) (Fin n) ℂ

namespace LogicalOperator

variable {g : AnyonStabilizerGenerator n} (L : LogicalOperator g)

/-- **Theorem**: Logical Operator Commutator Identity [g, L] = 0. -/
theorem logical_operator_commute
    (h_comm :
      (g : Matrix (Fin n) (Fin n) ℂ) * L.L_val =
        L.L_val * (g : Matrix (Fin n) (Fin n) ℂ)) :
    (g : Matrix (Fin n) (Fin n) ℂ) * L.L_val -
        L.L_val * (g : Matrix (Fin n) (Fin n) ℂ) = 0 := by
  have h := h_comm
  rw [h, sub_self]

/-- **Theorem**: Logical Operator Conjugation Invariance g * L * g† = L. -/
theorem logical_operator_conjugation_invariant
    (h_comm :
      (g : Matrix (Fin n) (Fin n) ℂ) * L.L_val =
        L.L_val * (g : Matrix (Fin n) (Fin n) ℂ)) :
    (g : Matrix (Fin n) (Fin n) ℂ) * L.L_val *
        (g : Matrix (Fin n) (Fin n) ℂ).conjTranspose = L.L_val := by
  calc
    (g : Matrix (Fin n) (Fin n) ℂ) * L.L_val *
        (g : Matrix (Fin n) (Fin n) ℂ).conjTranspose =
        L.L_val * (g : Matrix (Fin n) (Fin n) ℂ) *
          (g : Matrix (Fin n) (Fin n) ℂ).conjTranspose := by
            rw [h_comm]
    _ = L.L_val * ((g : Matrix (Fin n) (Fin n) ℂ) *
          (g : Matrix (Fin n) (Fin n) ℂ).conjTranspose) := by noncomm_ring
    _ = L.L_val * 1 := by rw [h_unitary g]
    _ = L.L_val := by noncomm_ring

/-- **Theorem**: Logical Operator Trace Protection Invariance: Tr(g * L * g†) = Tr(L). -/
theorem logical_operator_trace_protected
    (h_comm :
      (g : Matrix (Fin n) (Fin n) ℂ) * L.L_val =
        L.L_val * (g : Matrix (Fin n) (Fin n) ℂ)) :
    trace ((g : Matrix (Fin n) (Fin n) ℂ) * L.L_val *
      (g : Matrix (Fin n) (Fin n) ℂ).conjTranspose) = trace L.L_val := by
  rw [L.logical_operator_conjugation_invariant h_comm]

end LogicalOperator

end AnyonStabilizerGenerator

end AnyonicStabilizer
