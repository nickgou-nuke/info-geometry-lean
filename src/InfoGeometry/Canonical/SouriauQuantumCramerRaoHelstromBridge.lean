import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import InfoGeometry.Canonical.LandauerCramerRaoBoundBridge

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

open Matrix BigOperators

namespace SouriauQuantumCramerRao

variable {n : ℕ}

/-- 1. Symmetric Logarithmic Derivative (SLD) Condition: dρ/dθ = (1/2) (ρ L + L ρ) -/
def SymmetricLogarithmicDerivative (rho drho_dtheta L : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  drho_dtheta = (1 / 2 : ℝ) • (rho * L + L * rho)

/-- 2. Helstrom Quantum Fisher Information Metric: g_SLD = Tr(ρ L²) -/
def helstromQuantumFisherMetric (rho L : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  trace (rho * L * L)

/-- 🏆 THEOREM 1: Positivity of Helstrom Quantum Fisher Metric for Diagonal Density Matrix (ρᵢ ≥ 0) -/
theorem helstrom_quantum_fisher_pos (P L_diag : Fin n → ℝ) (hP : ∀ i, 0 ≤ P i) :
    0 ≤ helstromQuantumFisherMetric (diagonal P) (diagonal L_diag) := by
  dsimp [helstromQuantumFisherMetric]
  rw [diagonal_mul_diagonal, diagonal_mul_diagonal, trace_diagonal]
  refine Finset.sum_nonneg (fun i _ => ?_)
  have hp := hP i
  have hsq := mul_self_nonneg (L_diag i)
  nlinarith

/-- 🏆 THEOREM 2: Helstrom Quantum Cramér-Rao Lower Bound:
    Var(θ̂) ≥ 1 / Tr(ρ L²) when Var(θ̂) · Tr(ρ L²) ≥ 1 -/
theorem quantum_cramer_rao_bound (var fisherMetric : ℝ) (hI : 0 < fisherMetric)
    (hQCR : 1 ≤ var * fisherMetric) :
    1 / fisherMetric ≤ var := by
  rw [div_le_iff₀ hI]
  linarith

/-- 🏆 THEOREM 3: SLD Commutator Trace Neutrality: Tr(ρ L - L ρ) = 0 -/
theorem sld_commutator_trace_zero (rho L : Matrix (Fin n) (Fin n) ℝ) :
    trace (rho * L - L * rho) = 0 := by
  rw [trace_sub, trace_mul_comm L rho, sub_self]

end SouriauQuantumCramerRao
