import InfoGeometry.Canonical.Cl11CompatibleRealAlgebraicStateNet
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimit
import InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimitBridge

/-!
# Topological readout of the compatible real algebraic state net

The finite algebraic state net and the continuous inverse-family readout use
the same normalized trace.  This owner records that identification without
constructing a completed UHF algebra or a global state space.
-/

namespace InfoGeometry.Canonical.Cl11CompatibleRealAlgebraicStateNetTopological

open InfoGeometry.Canonical.Cl11CompatibleRealAlgebraicStateNet
open InfoGeometry.Canonical.Cl11FiniteNormalizedTraceState
open InfoGeometry.Canonical.Cl11CompatibleLocalStateNet
open InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimit
open InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimitBridge
open InfoGeometry.Canonical.Cl11TensorInductiveLimitTopologicalTrace
open InfoGeometry.Canonical.CliffordCARAlgebraicTopologicalComparison
open InfoGeometry.Canonical.CliffordCARTopologicalColimit
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Clifford.Cl11TensorTower

noncomputable section

/-- The compatible continuous readout extracted from the algebraic state net. -/
noncomputable def cl11CompatibleContinuousReadoutFamily :
    CompatibleContinuousReadoutFamily :=
  ⟨fun n =>
      (cl11CompatibleRealAlgebraicStateNet.state n).toContinuousLinearMap, by
    intro n
    ext X
    change cl11CompatibleRealAlgebraicStateNet.state n (stageRestrict n X) =
      cl11CompatibleRealAlgebraicStateNet.state (n + 1) X
    rw [state_eq_normalizedTrace, state_eq_normalizedTrace]
    exact normalizedTrace_stageRestrict n X⟩

@[simp] theorem cl11CompatibleContinuousReadoutFamily_apply
    (n : ℕ) (X : MatStage n) :
    cl11CompatibleContinuousReadoutFamily.1 n X =
      cl11CompatibleRealAlgebraicStateNet.state n X := rfl

theorem cl11CompatibleContinuousReadoutFamily_eq_normalizedTrace :
    cl11CompatibleContinuousReadoutFamily =
      normalizedTraceReadoutFamily := by
  apply Subtype.ext
  funext n
  ext X
  rfl

theorem cl11CompatibleContinuousReadoutFamily_compatible
    (n : ℕ) (X : MatStage (n + 1)) :
    cl11CompatibleContinuousReadoutFamily.1 n (stageRestrict n X) =
      cl11CompatibleContinuousReadoutFamily.1 (n + 1) X := by
  exact compatible_apply cl11CompatibleContinuousReadoutFamily n X

theorem algebraic_state_net_readout_is_continuous
    (n : ℕ) :
    Continuous
      (fun X : MatStage n =>
        cl11CompatibleRealAlgebraicStateNet.state n X) := by
  exact (cl11CompatibleContinuousReadoutFamily.1 n).continuous

theorem topological_colimit_readout_matches_algebraic_state
    (n : ℕ) (A : MatStage n) :
    normalizedTraceTopologicalColimitMap
        (algebraicToTopological (ofStage n A)) =
      cl11CompatibleRealAlgebraicStateNet.state n A := by
  rw [normalizedTraceColimitMap_matches_algebraic_stage]
  exact state_eq_normalizedTrace n A

end

end InfoGeometry.Canonical.Cl11CompatibleRealAlgebraicStateNetTopological
