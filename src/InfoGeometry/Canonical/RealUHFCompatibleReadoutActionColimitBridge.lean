import InfoGeometry.Canonical.RealUHFCompatibleReadoutDynamicsTopCatAction
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.RealUHFCompatibleReadoutColimitDynamicsBridge

/-!
# Action-level bridge from compatible readouts to the topological colimit

The scalar `TopCat` action on compatible readout families agrees with scalar
postcomposition of the normalized-trace colimit readout on every finite-stage
representative.  This is the precise action-level bridge; it does not assert a
global action on the colimit carrier itself.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealUHFCompatibleReadoutActionColimitBridge

open InfoGeometry.Canonical.RealUHFCompatibleReadoutDynamics
open InfoGeometry.Canonical.RealUHFCompatibleReadoutDynamicsTopCatAction
open InfoGeometry.Canonical.RealUHFCompatibleReadoutFamilyMorphism
open InfoGeometry.Canonical.RealUHFCompatibleReadoutScalarMorphism
open InfoGeometry.Canonical.RealUHFCompatibleReadoutScalarDynamicsBridge
open InfoGeometry.Canonical.RealUHFCompatibleReadoutColimitDynamicsBridge
open InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimit
open InfoGeometry.Canonical.Cl11TensorInductiveLimitTopologicalTrace
open InfoGeometry.Canonical.CliffordCARTopologicalColimit
open InfoGeometry.Clifford.Cl11TensorTower

theorem scalarDilationTopCatAction_normalizedTrace
    (t : ℝ) :
    scalarDilationTopCatAction t normalizedTraceReadoutFamily =
      mapFamily (scalarRescaling (Real.exp t)).map
        (scalarRescaling (Real.exp t)).map_compatibility
        normalizedTraceReadoutFamily := by
  simpa [scalarDilationTopCatAction] using
    (scalarRescaling_exp_matches_pullback t
      normalizedTraceReadoutFamily).symm

theorem normalizedTrace_action_coordinate
    (t : ℝ) (n : ℕ) (X : MatStage n) :
    (scalarDilationTopCatAction t normalizedTraceReadoutFamily).1 n X =
      scalarValueMap t
        (normalizedTraceTopologicalColimitMap
          (topologicalInjection n X)) := by
  rw [scalarDilationTopCatAction_normalizedTrace t]
  change (Real.exp t) • normalizedTrace n X =
    (Real.exp t) *
      normalizedTraceTopologicalColimitMap
        (topologicalInjection n X)
  rw [normalizedTraceTopologicalColimitMap_inclusion]
  rw [smul_eq_mul]

theorem normalizedTrace_action_coordinate_stageFlow
    (t : ℝ) (n : ℕ) (X : MatStage n) :
    (scalarDilationTopCatAction t normalizedTraceReadoutFamily).1 n X =
      normalizedTraceTopologicalColimitMap
        (topologicalInjection n
          (scalarDilationStageFlow.flow n t X)) := by
  calc
    (scalarDilationTopCatAction t normalizedTraceReadoutFamily).1 n X =
        scalarValueMap t
          (normalizedTraceTopologicalColimitMap
            (topologicalInjection n X)) :=
      normalizedTrace_action_coordinate t n X
    _ = normalizedTraceTopologicalColimitMap
          (topologicalInjection n
            (scalarDilationStageFlow.flow n t X)) :=
      normalizedTrace_scalarValueMap_matches_stageFlow t n X

end InfoGeometry.Canonical.RealUHFCompatibleReadoutActionColimitBridge
