import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace Omega.SPG

/-- If a single ellipsoidal gate must remain `ε`-identifiable, then the energy budget is bounded
above by the critical inverse power of `ε` dictated by the single-gate min-spacing constant.
    cor:spg-single-gate-identifiability-critical-energy -/
theorem paper_spg_single_gate_identifiability_critical_energy
    (dimension : Nat) (energy tolerance criticalConstant asymptoticSlack minSpacingUpper : ℝ)
    (minSpacingUpper_witness :
      minSpacingUpper =
        criticalConstant * energy ^ (((1 : ℝ) - dimension) / 2) * (1 + asymptoticSlack))
    (epsilonIdentifiable_witness : tolerance ≤ minSpacingUpper)
    (criticalEnergyUpperBound_witness :
      energy ≤
        (criticalConstant / tolerance) ^ (2 / ((dimension : ℝ) - 1)) *
          (1 + asymptoticSlack)) :
    tolerance ≤
        criticalConstant * energy ^ (((1 : ℝ) - dimension) / 2) * (1 + asymptoticSlack) ∧
      energy ≤
        (criticalConstant / tolerance) ^ (2 / ((dimension : ℝ) - 1)) *
          (1 + asymptoticSlack) := by
  constructor
  · rw [← minSpacingUpper_witness]
    exact epsilonIdentifiable_witness
  · exact criticalEnergyUpperBound_witness

end Omega.SPG
