import Mathlib.Tactic
import Omega.PhysicalSpacetimeSkeleton.AdmissibleGlobalEinsteinEquation
import Omega.PhysicalSpacetimeSkeleton.ResourceScalarWellDefined

namespace Omega.PhysicalSpacetimeSkeleton

/-- In the pure-trace resource sector, inserting the constant residual Lagrangian into the
stress-energy definition leaves only a metric multiple, so the traceless part vanishes.
    thm:physical-spacetime-resource-stress-energy-pure-trace -/
theorem paper_physical_spacetime_resource_stress_energy_pure_trace
    (metric residualLagrangian stressEnergy tracelessPart : ℝ)
    (stressEnergy_eq : stressEnergy = residualLagrangian * metric)
    (tracelessPart_eq : tracelessPart = stressEnergy - residualLagrangian * metric) :
    stressEnergy = residualLagrangian * metric ∧ tracelessPart = 0 := by
  refine ⟨stressEnergy_eq, ?_⟩
  rw [tracelessPart_eq, stressEnergy_eq]
  ring

end Omega.PhysicalSpacetimeSkeleton
