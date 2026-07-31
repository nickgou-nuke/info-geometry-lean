import Mathlib.Tactic
import Omega.PhysicalSpacetimeSkeleton.EffectiveCosmologicalClosure
import Omega.PhysicalSpacetimeSkeleton.ResourceStressEnergyPureTrace
import Omega.PhysicalSpacetimeSkeleton.WeakFieldQuadraticHarmonicNormalForm

namespace Omega.PhysicalSpacetimeSkeleton

/-- Package the pure-trace stress reduction, effective cosmological closure, and weak-field
quadratic-harmonic normal form into the statement that no independent localized matter source
survives inside the admissible closure. -/
theorem paper_physical_spacetime_no_localized_matter_source_package
    (metric residualLagrangian stressEnergy tracelessPart : ℝ)
    (stressEnergy_eq : stressEnergy = residualLagrangian * metric)
    (tracelessPart_eq : tracelessPart = stressEnergy - residualLagrangian * metric)
    (E : AdmissibleEinsteinClosure) (hAdm : E.admissible)
    (hMetric : E.metric = metric) (hResidual : E.residualLagrangian = residualLagrangian)
    (hStress : E.stressEnergy = stressEnergy)
    (Delta : (Fin 3 → Real) →ₗ[Real] Real) (phi q : Fin 3 → Real) (sigma L : Real)
    (hq : Delta q = sigma * L) (hphi : Delta phi = sigma * L) :
    tracelessPart = 0 ∧
      E.einsteinTensor +
          (E.cosmologicalConstant - E.couplingConstant * E.residualLagrangian) * E.metric =
        0 ∧
      ∃ h : Fin 3 → Real, phi = q + h ∧ Delta h = 0 := by
  have hPureD := paper_physical_spacetime_resource_stress_energy_pure_trace
    metric residualLagrangian stressEnergy tracelessPart stressEnergy_eq tracelessPart_eq
  rcases hPureD with ⟨hPureStress, hTraceZero⟩
  have hPureE : E.stressEnergy = E.residualLagrangian * E.metric := by
    rw [hStress, hPureStress, hResidual, hMetric]
  refine ⟨hTraceZero, paper_physical_spacetime_effective_cosmological_closure E hAdm hPureE, ?_⟩
  exact paper_physical_spacetime_weak_field_quadratic_harmonic_normal_form Delta phi q sigma L hq
    hphi

/-- Paper label wrapper for the no-localized-matter-source corollary.
    cor:physical-spacetime-no-localized-matter-source -/
def paper_physical_spacetime_no_localized_matter_source : Prop := by
  exact
    ∀ (metric residualLagrangian stressEnergy tracelessPart : Real)
      (_stressEnergy_eq : stressEnergy = residualLagrangian * metric)
      (_tracelessPart_eq : tracelessPart = stressEnergy - residualLagrangian * metric)
      (E : AdmissibleEinsteinClosure) (_hAdm : E.admissible)
      (_hMetric : E.metric = metric) (_hResidual : E.residualLagrangian = residualLagrangian)
      (_hStress : E.stressEnergy = stressEnergy) (Delta : (Fin 3 → Real) →ₗ[Real] Real)
      (phi q : Fin 3 → Real) (sigma L : Real), Delta q = sigma * L →
        Delta phi = sigma * L →
        tracelessPart = 0 ∧
          E.einsteinTensor +
              (E.cosmologicalConstant - E.couplingConstant * E.residualLagrangian) * E.metric =
            0 ∧
          ∃ h : Fin 3 → Real, phi = q + h ∧ Delta h = 0

theorem paper_physical_spacetime_no_localized_matter_source_verified :
    paper_physical_spacetime_no_localized_matter_source := by
  intro metric residualLagrangian stressEnergy tracelessPart stressEnergy_eq tracelessPart_eq
    E hAdm hMetric hResidual hStress Delta phi q sigma L hq hphi
  exact paper_physical_spacetime_no_localized_matter_source_package
    metric residualLagrangian stressEnergy tracelessPart stressEnergy_eq tracelessPart_eq
    E hAdm hMetric hResidual hStress Delta phi q sigma L hq hphi

end Omega.PhysicalSpacetimeSkeleton
