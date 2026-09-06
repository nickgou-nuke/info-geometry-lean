import Mathlib.Data.Real.Basic

noncomputable section

namespace QCD_Instanton

variable {V : ℝ} (hV : V > 0)
variable {N_f N_c : ℕ} (hN : N_c = 3)

/-- Topological susceptibility from Veneziano-Witten formula -/
def topological_susceptibility (f_pi m_eta m_eta_prime m_K : ℝ) : ℝ :=
  (f_pi^2 / (2 * N_f)) * (m_eta^2 + m_eta_prime^2 - 2 * m_K^2)

/-- Instanton liquid effective parameters -/
structure InstantonLiquid where
  rho_bar : ℝ      -- average size (fm)
  density : ℝ      -- instantons per fm^4
  
def Negele_Vacuum : InstantonLiquid :=
  { rho_bar := 0.33, density := 1 }

/-- The Negele vacuum has a positive density -/
theorem negele_vacuum_density_pos : Negele_Vacuum.density > 0 := by
  dsimp [Negele_Vacuum]
  exact zero_lt_one

end QCD_Instanton
end noncomputable section
