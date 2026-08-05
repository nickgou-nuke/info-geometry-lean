import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace InfoGeometry.Canonical

open Real
open scoped BigOperators

variable {α : Type*} [Fintype α]

/-- The spectral partition function Z_rho(s) = Tr(rho^s) -/
noncomputable def Z_rho (ρ : α → ℝ) (s : ℝ) : ℝ :=
  ∑ i, (ρ i) ^ s

/-- The modular log-generating function Psi_rho(s) = log Z_rho(s) -/
noncomputable def Psi_rho (ρ : α → ℝ) (s : ℝ) : ℝ :=
  log (Z_rho ρ s)

/-- The escort state at order s -/
noncomputable def escort_state (ρ : α → ℝ) (s : ℝ) (i : α) : ℝ :=
  (ρ i) ^ s / Z_rho ρ s

end InfoGeometry.Canonical
