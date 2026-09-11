import InfoGeometry.Canonical.RealUHFCompatibleReadoutTopologicalDescent
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.RealUHFCompatibleReadoutColimitAction

/-!
# Colimit action/readout compatibility

The scalar action on the topological colimit and the scaled normalized-trace
readout agree on every finite-stage injection.  The colimit universal
property upgrades this stage calculation to a morphism equality.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealUHFCompatibleReadoutColimitActionBridge

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Canonical.Cl11TensorInductiveLimitTopologicalTrace
open InfoGeometry.Canonical.CliffordCARTopologicalColimit
open InfoGeometry.Canonical.RealUHFCompatibleReadoutColimitAction
open InfoGeometry.Canonical.RealUHFCompatibleReadoutColimitDynamicsBridge
open InfoGeometry.Canonical.RealUHFCompatibleReadoutDynamics
open InfoGeometry.Canonical.RealUHFCompatibleReadoutTopologicalDescent
open InfoGeometry.Clifford.Cl11TensorTower
open FilteredColimit.Native.Topological

theorem scalarDilationTopologicalColimitAction_normalizedTrace
    (t : ℝ) :
    scalarDilationTopologicalColimitAction t ≫
        normalizedTraceTopologicalColimitMap =
      normalizedTraceReadoutAtTime t := by
  apply topologicalDirectDescend_unique topologicalDiagram
    (normalizedTraceScaledTopologicalCocone t)
    (scalarDilationTopologicalColimitAction t ≫
      normalizedTraceTopologicalColimitMap)
  intro n
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro A
  change normalizedTraceTopologicalColimitMap
      (scalarDilationTopologicalColimitAction t
        (topologicalInjection n A)) =
    (normalizedTraceScaledTopologicalCocone t).ι.app n A
  rw [scalarDilationTopologicalColimitAction_inclusion,
    normalizedTraceTopologicalColimitMap_inclusion]
  change normalizedTrace n
      (scalarDilationStageFlow.flow n t A) =
    (Real.exp t) * normalizedTrace n A
  simpa only [scalarDilationStageFlow_apply, smul_eq_mul] using
    (normalizedTraceReadout_scalarDilation t n A)

theorem scalarDilationTopologicalColimitAction_normalizedTrace_postcomposition
    (t : ℝ) :
    scalarDilationTopologicalColimitAction t ≫
        normalizedTraceTopologicalColimitMap =
      normalizedTraceTopologicalColimitMap ≫ scalarValueMap t := by
  rw [scalarDilationTopologicalColimitAction_normalizedTrace,
    normalizedTraceReadoutAtTime_eq_postcomposition]

end InfoGeometry.Canonical.RealUHFCompatibleReadoutColimitActionBridge
end
