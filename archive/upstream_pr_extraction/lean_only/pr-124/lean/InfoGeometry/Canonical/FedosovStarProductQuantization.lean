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

namespace FedosovStarProduct

variable {n : ℕ} [Fintype (Fin n)] [DecidableEq (Fin n)]

/-- Fedosov Deformation Star Product A ⋆_hbar B = A * B + hbar • (A * θ * B). -/
def starProduct (hbar : ℂ) (theta A B : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  A * B + hbar • (A * theta * B)

/-- **Theorem**: Classical Limit hbar = 0 reduces Star Product to standard Matrix Product: A ⋆_0 B = A * B. -/
theorem star_product_classical_limit (theta A B : Matrix (Fin n) (Fin n) ℂ) :
    starProduct 0 theta A B = A * B := by
  dsimp [starProduct]
  rw [zero_smul, add_zero]

/-- Deformed Star Commutator [A, B]_star = A ⋆_hbar B - B ⋆_hbar A. -/
def starCommutator (hbar : ℂ) (theta A B : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  starProduct hbar theta A B - starProduct hbar theta B A

/-- **Theorem**: Star Commutator Linearity in hbar: [A, B]_star = [A, B] + hbar • (A θ B - B θ A). -/
theorem star_commutator_expansion (hbar : ℂ) (theta A B : Matrix (Fin n) (Fin n) ℂ) :
    starCommutator hbar theta A B = (A * B - B * A) + hbar • (A * theta * B - B * theta * A) := by
  dsimp [starCommutator, starProduct]
  rw [smul_sub]
  noncomm_ring

/-- **Theorem**: Fedosov Star Product Trace Linear Contribution: Tr(A ⋆_hbar B) = Tr(A B) + hbar * Tr(A θ B). -/
theorem star_product_trace (hbar : ℂ) (theta A B : Matrix (Fin n) (Fin n) ℂ) :
    trace (starProduct hbar theta A B) = trace (A * B) + hbar * trace (A * theta * B) := by
  dsimp [starProduct]
  rw [trace_add, trace_smul, smul_eq_mul]

/-- **Theorem**: Tracial Zero Poisson Structure θ = 0 restores exact Trace Preservation Tr(A ⋆_hbar B) = Tr(A B). -/
theorem star_product_trace_zero_poisson (hbar : ℂ) (A B : Matrix (Fin n) (Fin n) ℂ) :
    trace (starProduct hbar 0 A B) = trace (A * B) := by
  dsimp [starProduct]
  rw [mul_zero, zero_mul, smul_zero, add_zero]

end FedosovStarProduct
