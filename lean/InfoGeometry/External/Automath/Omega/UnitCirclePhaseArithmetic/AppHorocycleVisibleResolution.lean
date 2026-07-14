import Mathlib.Tactic
import InfoGeometry.External.Automath.Omega.UnitCirclePhaseArithmetic.AppBusemannPoissonMinusOne
import InfoGeometry.External.Automath.Omega.UnitCirclePhaseArithmetic.HorocycleFoliationMinusOne
import InfoGeometry.External.Automath.Omega.Zeta.OffcriticalHorocycleBusemann

namespace Omega.UnitCirclePhaseArithmetic

/-- Paper label: `cor:app-horocycle-visible-resolution`. The off-critical visibility hypothesis is
the explicit boundary-depth inequality, and the previously established horocycle/Busemann
identifications rewrite that depth as the endpoint-resolution bound. -/
theorem paper_app_horocycle_visible_resolution (γ δ ρ : ℝ) (hδ : 0 < δ)
    (hvis : 1 - ρ < Omega.Zeta.appOffcriticalBoundaryDepth γ δ) :
    1 - ρ < 4 * δ / (γ ^ 2 + (1 + δ) ^ 2) := by
  let _ := paper_app_busemann_poisson_minus1 γ δ hδ
  let _ := paper_app_horocycle_foliation_minus1 hδ
  have hresolution : Omega.Zeta.appOffcriticalBoundaryDepth γ δ = 4 * δ / (γ ^ 2 + (1 + δ) ^ 2) := by
    rcases Omega.Zeta.paper_app_offcritical_horocycle_busemann γ δ hδ with ⟨_, hdepth⟩
    calc
      Omega.Zeta.appOffcriticalBoundaryDepth γ δ = δ * (4 / (γ ^ 2 + (1 + δ) ^ 2)) := hdepth
      _ = 4 * δ / (γ ^ 2 + (1 + δ) ^ 2) := by ring_nf
  rw [hresolution] at hvis
  exact hvis

end Omega.UnitCirclePhaseArithmetic
