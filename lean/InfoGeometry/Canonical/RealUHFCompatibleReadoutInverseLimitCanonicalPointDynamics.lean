import InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitCanonicalPoint
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitDynamics
import InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitContinuousAction

/-!
# Dynamics of the distinguished inverse-limit point

The scalar-dilation action is specialized to the canonical normalized-trace
point.  The result is stated through finite coordinates, which is the native
limit API and does not assert invariance, KMS structure, or completion-level
automorphisms.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitCanonicalPointDynamics

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimit
open InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitCanonicalPoint
open InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitDynamics
open InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitContinuousAction
open InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitObservables
open InfoGeometry.Canonical.RealUHFCompatibleReadoutDynamics
open InfoGeometry.Canonical.RealUHFCompatibleReadoutStageActionTopCat
open InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimit
open InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimitTopCat
open InfoGeometry.Clifford.Cl11TensorTower

theorem normalizedTraceInverseLimitPoint_action_projection
    (t : ℝ) (n : ℕ) :
    (limit.π readoutDiagram n)
        (scalarDilationReadoutInverseLimitAction t
          normalizedTraceInverseLimitPoint) =
      (stageReadoutActionTopCatHom n t)
        (normalizedTraceReadoutFamily.1 n) := by
  rw [scalarDilationReadoutInverseLimitAction_projection_apply]
  rw [normalizedTraceInverseLimitPoint_projection]

theorem normalizedTraceInverseLimitPoint_action_projection_explicit
    (t : ℝ) (n : ℕ) :
    (limit.π readoutDiagram n)
        (scalarDilationReadoutInverseLimitAction t
          normalizedTraceInverseLimitPoint) =
      (Real.exp t) • normalizedTraceReadoutFamily.1 n := by
  rw [normalizedTraceInverseLimitPoint_action_projection]
  change stageReadoutActionContinuous n t
      (normalizedTraceReadoutFamily.1 n) = _
  ext X
  simp [stageReadoutActionContinuous_apply,
    scalarDilationStageFlow_apply]

theorem normalizedTraceInverseLimitPoint_action_zero :
    scalarDilationReadoutInverseLimitAction 0
        normalizedTraceInverseLimitPoint =
      normalizedTraceInverseLimitPoint := by
  have h := congrArg
    (fun f => f normalizedTraceInverseLimitPoint)
    scalarDilationReadoutInverseLimitAction_zero
  simpa using h

theorem normalizedTraceInverseLimitPoint_action_add
    (s t : ℝ) :
    scalarDilationReadoutInverseLimitAction (s + t)
        normalizedTraceInverseLimitPoint =
      scalarDilationReadoutInverseLimitAction t
        (scalarDilationReadoutInverseLimitAction s
          normalizedTraceInverseLimitPoint) := by
  have h := congrArg
    (fun f => f normalizedTraceInverseLimitPoint)
    (scalarDilationReadoutInverseLimitAction_add s t)
  simpa [CategoryTheory.Category.assoc] using h

theorem continuous_normalizedTraceInverseLimitPoint_orbit :
    Continuous (fun t : ℝ =>
      scalarDilationReadoutInverseLimitAction t
        normalizedTraceInverseLimitPoint) := by
  exact continuous_scalarDilationReadoutInverseLimitAction_orbit
    normalizedTraceInverseLimitPoint

theorem continuous_normalizedTraceInverseLimitPoint_evaluation_time
    (n : ℕ) (X : MatStage n) :
    Continuous (fun t : ℝ =>
      inverseLimitStageEvaluationTopCatHom n X
        (scalarDilationReadoutInverseLimitAction t
          normalizedTraceInverseLimitPoint)) := by
  exact continuous_inverseLimitStageEvaluation_time
    normalizedTraceInverseLimitPoint n X

end InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitCanonicalPointDynamics
end
