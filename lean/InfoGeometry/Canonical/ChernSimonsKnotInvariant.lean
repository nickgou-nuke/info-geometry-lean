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

noncomputable section

open Matrix Complex

namespace ChernSimonsKnot

variable {n : ℕ} [Fintype (Fin n)] [DecidableEq (Fin n)]

/-- Gauge Transformation Conjugation of Wilson Loop Matrix W by Unitary Gauge Matrix U with U * U_inv = 1. -/
def wilsonLoopGaugeTransform (W U U_inv : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  U * W * U_inv

/-- **Theorem**: Gauge Invariance of Wilson Loop Trace: Tr(U * W * U⁻¹) = Tr(W). -/
theorem wilson_loop_trace_gauge_invariant (W U U_inv : Matrix (Fin n) (Fin n) ℂ)
    (h_inv : U_inv * U = 1) :
    trace (wilsonLoopGaugeTransform W U U_inv) = trace W := by
  dsimp [wilsonLoopGaugeTransform]
  have h_comm : trace (U * W * U_inv) = trace (U_inv * (U * W)) := trace_mul_comm (U * W) U_inv
  rw [h_comm]
  have h_assoc : U_inv * (U * W) = (U_inv * U) * W := by noncomm_ring
  rw [h_assoc, h_inv, one_mul]

/-- Chern-Simons Skein Relation Matrix Linear Combination q^(1/2) * L_plus - q^(-1/2) * L_minus. -/
def skeinLinearCombination (q_sqrt L_plus L_minus : ℂ) : ℂ :=
  q_sqrt * L_plus - (1 / q_sqrt) * L_minus

/-- **Theorem**: Skein Relation Unknot Factorization Identity for equal link projections L_plus = L_minus = L_zero:
    q^(1/2) * L₀ - q^(-1/2) * L₀ = (q^(1/2) - q^(-1/2)) * L₀. -/
theorem skein_relation_factorization (q_sqrt L_zero : ℂ) (hq : q_sqrt ≠ 0) :
    skeinLinearCombination q_sqrt L_zero L_zero = (q_sqrt - 1 / q_sqrt) * L_zero := by
  dsimp [skeinLinearCombination]
  ring

end ChernSimonsKnot
