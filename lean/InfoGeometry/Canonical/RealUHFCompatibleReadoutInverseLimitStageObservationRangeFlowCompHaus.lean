import InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitStageObservationRangeCompHaus
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitStageObservationRangeFlowHomeomorph

/-!
# Compact-Hausdorff packaging of scalar-flow transport on observation ranges

The finite-stage observation-range flow homeomorphism is promoted to a
`CompHaus` isomorphism under explicit compactness and Hausdorff hypotheses on
the inverse-limit carrier.  This owner does not assert compactness of the
full inverse limit or any analytic completion.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitStageObservationRangeFlowCompHaus

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimit
open InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitStageObservationTopCat
open InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitStageObservationRangeTopCat
open InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitStageObservationRangeCompHaus
open InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitStageObservationRangeFlowHomeomorph
open InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitSymbolicLatentFlow
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Topology

abbrev inverseLimitCarrier := (limit readoutDiagram).carrier
abbrev flow := scalarDilationSymbolicLatentFlow

variable [CompactSpace inverseLimitCarrier] [T2Space inverseLimitCarrier]

noncomputable def stageObservationRangeFlowCompHausIso
    (ρ : inverseLimitCarrier) (n : ℕ) (X : MatStage n) (t : ℝ) :
    stageObservationRangeCompHaus ρ n X ≅
      stageObservationRangeCompHaus (flow.act t ρ) n X := by
  let e := stageObservationRangeFlowHomeomorph ρ n X t
  exact
    { hom := ⟨TopCat.ofHom
        { toFun := e
          continuous_toFun := e.continuous }⟩
      inv := ⟨TopCat.ofHom
        { toFun := e.symm
          continuous_toFun := e.symm.continuous }⟩
      hom_inv_id := by
        apply ConcreteCategory.hom_ext
        intro z
        change e.symm (e z) = z
        exact e.symm_apply_apply z
      inv_hom_id := by
        apply ConcreteCategory.hom_ext
        intro z
        change e (e.symm z) = z
        exact e.apply_symm_apply z }

@[simp] theorem stageObservationRangeFlowCompHausIso_hom_apply
    (ρ : inverseLimitCarrier) (n : ℕ) (X : MatStage n) (t : ℝ)
    (z : stageObservationRangeCompHaus ρ n X) :
    (stageObservationRangeFlowCompHausIso ρ n X t).hom z =
      ⟨Real.exp t * z.1, (stageObservationRangeFlowHomeomorph ρ n X t z).property⟩ := by
  rfl

theorem stageObservationRangeFlowCompHausIso_hom_forget
    (ρ : inverseLimitCarrier) (n : ℕ) (X : MatStage n) (t : ℝ) :
    compHausToTop.map (stageObservationRangeFlowCompHausIso ρ n X t).hom =
      TopCat.ofHom
        { toFun := stageObservationRangeFlowHomeomorph ρ n X t
          continuous_toFun := (stageObservationRangeFlowHomeomorph ρ n X t).continuous } := by
  rfl

theorem stageObservationRangeFlowCompHausIso_trans_apply
    (ρ : inverseLimitCarrier) (n : ℕ) (X : MatStage n) (s t : ℝ)
    (z : stageObservationRangeCompHaus ρ n X) :
    (((stageObservationRangeFlowCompHausIso ρ n X t).hom ≫
        (stageObservationRangeFlowCompHausIso (flow.act t ρ) n X s).hom) z).1 =
      ((stageObservationRangeFlowCompHausIso ρ n X (s + t)).hom z).1 := by
  exact stageObservationRangeFlowHomeomorph_trans_apply ρ n X s t z

end InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitStageObservationRangeFlowCompHaus
end
