import Mathlib.Data.Real.Basic
import InfoGeometry.Canonical.ModularLogGenerating

namespace InfoGeometry.Canonical

open Real

variable {α : Type*} [Fintype α]

/-- The Rényi entropy of order s ≠ 1 -/
noncomputable def S_R_renyi (ρ : α → ℝ) (k_B s : ℝ) : ℝ :=
  (k_B / (1 - s)) * Psi_rho ρ s

/-- Rényi entropy is the secant of the modular potential -/
theorem S_R_eq_secant_Psi (ρ : α → ℝ) (k_B s : ℝ) :
    S_R_renyi ρ k_B s = (k_B / (1 - s)) * Psi_rho ρ s := by
  rfl

end InfoGeometry.Canonical
