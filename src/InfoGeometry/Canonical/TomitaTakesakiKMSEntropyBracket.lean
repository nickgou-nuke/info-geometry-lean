import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import InfoGeometry.Canonical.TomitaTakesakiCommutantBridge

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

open Matrix BigOperators

namespace TomitaTakesakiKMSEntropy

variable {n : ℕ}

/-- 1. Non-Commutative Hamiltonian Commutator Bracket [H, ρ] = H ρ - ρ H -/
def hamiltonianCommutator (H rho : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  H * rho - rho * H

/-- 🏆 THEOREM 1: Hamiltonian Evolution Trace Conservation: Tr([H, ρ]) = 0 -/
theorem hamiltonian_trace_nullity (H rho : Matrix (Fin n) (Fin n) ℝ) :
    trace (hamiltonianCommutator H rho) = 0 := by
  dsimp [hamiltonianCommutator]
  rw [trace_sub, trace_mul_comm H rho, sub_self]

/-- 2. Lindblad Dissipation Generator D[L](ρ) = L ρ Lᵀ - (1/2) {Lᵀ L, ρ} -/
noncomputable def lindbladDissipator (L rho : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  L * rho * L.transpose - (1 / 2 : ℝ) • (L.transpose * L * rho + rho * L.transpose * L)

/-- 🏆 THEOREM 2: Trace Preservation under Lindblad Dissipation: Tr(D[L](ρ)) = 0 -/
theorem lindblad_trace_preservation (L rho : Matrix (Fin n) (Fin n) ℝ) :
    trace (lindbladDissipator L rho) = 0 := by
  dsimp [lindbladDissipator]
  have h_comm1 : trace (L * rho * L.transpose) = trace (L.transpose * L * rho) := by
    calc trace (L * rho * L.transpose) = trace (L.transpose * (L * rho)) := by rw [trace_mul_comm]
      _ = trace (L.transpose * L * rho) := by rw [Matrix.mul_assoc]
  have h_comm2 : trace (rho * L.transpose * L) = trace (L.transpose * L * rho) := by
    calc trace (rho * L.transpose * L) = trace (L * (rho * L.transpose)) := by rw [trace_mul_comm]
      _ = trace (L * rho * L.transpose) := by rw [← Matrix.mul_assoc]
      _ = trace (L.transpose * L * rho) := h_comm1
  rw [trace_sub, trace_smul, trace_add, h_comm2, h_comm1, smul_eq_mul]
  ring

/-- 🏆 THEOREM 3: Metriplectic Bracket Conservation-Dissipation Dual Decomposition:
    dρ/dt = -i [H, ρ] + D[L](ρ) preserves total probability trace Tr(dρ/dt) = 0 -/
theorem metriplectic_total_trace_preservation (H L rho : Matrix (Fin n) (Fin n) ℝ) :
    trace (hamiltonianCommutator H rho + lindbladDissipator L rho) = 0 := by
  rw [trace_add, hamiltonian_trace_nullity, lindblad_trace_preservation, add_zero]

end TomitaTakesakiKMSEntropy
