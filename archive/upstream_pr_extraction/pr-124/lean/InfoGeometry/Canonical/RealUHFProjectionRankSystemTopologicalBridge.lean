import InfoGeometry.Canonical.RealUHFProjectionRankSystemTopological
import InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimit

/-!
# Bridge from finite normalized trace maps to the compatible-family carrier

This owner identifies the continuous normalized trace at each finite matrix
stage with the corresponding coordinate of the existing compatible readout
family.  It proves only the restriction naturality of that readout; it does
not identify the family with a state space, a completed UHF algebra, or
`K₀`/`KO₀`.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealUHFProjectionRankSystemTopologicalBridge

open InfoGeometry.Canonical
open InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimit
open InfoGeometry.Canonical.RealUHFProjectionRankSystemTopological
open InfoGeometry.Clifford.Cl11TensorTower

theorem finiteStageNormalizedTraceCLM_eq_compatible_coordinate
    (n : ℕ) :
    finiteStageNormalizedTraceCLM n =
      normalizedTraceReadoutFamily.1 n := by
  rfl

theorem finiteStageNormalizedTraceCLM_restriction_natural
    (n : ℕ) :
    (finiteStageNormalizedTraceCLM n).comp (stageRestrictCLM n) =
      finiteStageNormalizedTraceCLM (n + 1) := by
  rw [finiteStageNormalizedTraceCLM_eq_compatible_coordinate,
    finiteStageNormalizedTraceCLM_eq_compatible_coordinate]
  exact normalizedTraceReadoutFamily.2 n

theorem finiteStageNormalizedTraceCLM_restriction_natural_apply
    (n : ℕ) (X : MatStage (n + 1)) :
    finiteStageNormalizedTraceCLM n (stageRestrictCLM n X) =
      finiteStageNormalizedTraceCLM (n + 1) X := by
  have h := congrArg
    (fun f : MatStage (n + 1) →L[ℝ] ℝ => f X)
    (finiteStageNormalizedTraceCLM_restriction_natural n)
  exact h

end RealUHFProjectionRankSystemTopologicalBridge

end Canonical
