import Mathlib.Data.Real.Basic
import InfoGeometry.Canonical.RenyiFromModularPowers
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace InfoGeometry.Canonical

open Real
open scoped BigOperators

variable {α : Type*} [Fintype α]

/-- The macrostate multiplicity Omega -/
noncomputable def Omega_multiplicity (P_M : α → ℝ) : ℝ :=
  ∑ i, P_M i

/-- Boltzmann entropy S_B = k_B log Omega -/
noncomputable def S_B_boltzmann (P_M : α → ℝ) (k_B : ℝ) : ℝ :=
  k_B * log (Omega_multiplicity P_M)

/-- The microcanonical state rho_M -/
noncomputable def rho_M (P_M : α → ℝ) (i : α) : ℝ :=
  P_M i / Omega_multiplicity P_M

end InfoGeometry.Canonical
