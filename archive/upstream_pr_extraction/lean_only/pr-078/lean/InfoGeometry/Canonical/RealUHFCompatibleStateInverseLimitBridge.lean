import InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimit
import InfoGeometry.Canonical.Cl11TensorInductiveLimitTopologicalTrace

/-!
# Bridge from the real projective readout family to the `TopCat` colimit

The projective family uses the block restriction maps, while the topological
colimit uses the forward matrix embeddings.  They are not identified as the
same limiting object here.  Their common normalized-trace stage readout is
the precise bridge between the two constructions.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimitBridge

open CategoryTheory
open InfoGeometry.Canonical.CliffordCARAlgebraicTopologicalComparison
open InfoGeometry.Canonical.Cl11TensorInductiveLimitTopologicalTrace
open InfoGeometry.Canonical.Cl11TensorInductiveLimitTopologicalComparison
open InfoGeometry.Canonical.CliffordCARTopologicalColimit
open InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimit
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11TensorTowerLimit

theorem normalizedTraceColimitMap_matches_inverse_family
    (n : ℕ) (A : MatStage n) :
    normalizedTraceTopologicalColimitMap
        (topologicalInjection n A) =
      normalizedTraceReadoutFamily.1 n A := by
  rw [normalizedTraceTopologicalColimitMap_inclusion,
    normalizedTraceReadoutFamily_apply]

theorem normalizedTraceColimitMap_unique_from_inverse_family
    (f : topologicalColimit ⟶ TopCat.of ℝ)
    (hf : ∀ (n : ℕ) (A : MatStage n),
      f (topologicalInjection n A) =
        normalizedTraceReadoutFamily.1 n A) :
    f = normalizedTraceTopologicalColimitMap := by
  apply normalizedTraceTopologicalColimitMap_unique
  intro n A
  rw [hf n A, normalizedTraceReadoutFamily_apply]

theorem normalizedTraceColimitMap_matches_algebraic_stage
    (n : ℕ) (A : MatStage n) :
    normalizedTraceTopologicalColimitMap
        (algebraicToTopological (ofStage n A)) =
      normalizedTraceReadoutFamily.1 n A := by
  rw [normalizedTraceTopologicalColimitMap_algebraic_stage,
    normalizedTraceReadoutFamily_apply]

end InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimitBridge

end
