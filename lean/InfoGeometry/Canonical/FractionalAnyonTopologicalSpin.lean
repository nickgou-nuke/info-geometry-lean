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

namespace FractionalAnyonSpin

variable {n : ℕ} [DecidableEq (Fin n)]

/-- Non-Abelian Anyonic Fractional Statistics System with Single Braid R_ab and Reverse Braid R_ba. -/
structure AnyonBraidSystem (n : ℕ) [DecidableEq (Fin n)] where
  R_ab : Matrix (Fin n) (Fin n) ℂ
  R_ba : Matrix (Fin n) (Fin n) ℂ
  h_Rab_unitary : R_ab * R_ab.conjTranspose = 1
  h_Rba_unitary : R_ba * R_ba.conjTranspose = 1
  h_comm_braid : R_ab * R_ba = R_ba * R_ab

namespace AnyonBraidSystem

variable (sys : AnyonBraidSystem n)

/-- Double Braiding Anyon Monodromy Operator M_ab = R_ba * R_ab. -/
def doubleBraidingOperator : Matrix (Fin n) (Fin n) ℂ :=
  sys.R_ba * sys.R_ab

/-- **Theorem**: Double Braiding Monodromy Unitarity: M_ab * M_ab† = 1. -/
theorem double_braiding_unitary :
    sys.doubleBraidingOperator * sys.doubleBraidingOperator.conjTranspose = 1 := by
  dsimp [doubleBraidingOperator]
  rw [conjTranspose_mul]
  calc (sys.R_ba * sys.R_ab) * (sys.R_ab.conjTranspose * sys.R_ba.conjTranspose)
    _ = sys.R_ba * (sys.R_ab * sys.R_ab.conjTranspose) * sys.R_ba.conjTranspose := by noncomm_ring
    _ = sys.R_ba * 1 * sys.R_ba.conjTranspose := by rw [sys.h_Rab_unitary]
    _ = sys.R_ba * sys.R_ba.conjTranspose := by rw [mul_one]
    _ = 1 := sys.h_Rba_unitary

/-- **Theorem**: Double Braiding Monodromy Trace Normalization: Tr(M_ab M_ab†) = n. -/
theorem double_braiding_trace_normalized :
    trace (sys.doubleBraidingOperator * sys.doubleBraidingOperator.conjTranspose) = (n : ℂ) := by
  rw [sys.double_braiding_unitary, trace_one, Fintype.card_fin]

/-- **Theorem**: Monodromy Gauge Action Trace Invariance: Tr(U M_ab U⁻¹) = Tr(M_ab). -/
theorem double_braiding_gauge_trace_invariant (U U_inv : Matrix (Fin n) (Fin n) ℂ) (h_inv : U_inv * U = 1) :
    trace (U * sys.doubleBraidingOperator * U_inv) = trace sys.doubleBraidingOperator := by
  have h_comm : trace (U * sys.doubleBraidingOperator * U_inv) = trace (U_inv * (U * sys.doubleBraidingOperator)) := trace_mul_comm (U * sys.doubleBraidingOperator) U_inv
  rw [h_comm]
  have h_assoc : U_inv * (U * sys.doubleBraidingOperator) = (U_inv * U) * sys.doubleBraidingOperator := by
    rw [← Matrix.mul_assoc]
  rw [h_assoc, h_inv, one_mul]

end AnyonBraidSystem

end FractionalAnyonSpin
