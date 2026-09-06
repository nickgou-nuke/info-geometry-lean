import InfoGeometry.Canonical.RealUHFCompatibleInverseLimitObservableComparison
import InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitStageObservationRangeCompHaus
import InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitStageObservationRangeFlowCompHaus
import Mathlib.Topology.Category.CompHaus.Basic

/-!
# Compact-Hausdorff packaging of canonical observation-range transport

The canonical comparison between compatible readout families and the native
inverse-limit carrier restricts to a map into the native finite-stage
observation range.  Compactness is assumed only where `CompHaus` requires it;
this file does not make the full inverse-limit carrier compact.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealUHFCompatibleInverseLimitObservableRangeCompHaus

open CategoryTheory
open CategoryTheory.Limits
open InfoGeometry.Canonical.RealUHFCompatibleInverseLimitFlowComparison
open InfoGeometry.Canonical.RealUHFCompatibleInverseLimitObservableComparison
open InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimit
open InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitStageObservationTopCat
open InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitStageObservationRangeCompHaus
open InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitStageObservationRangeFlowCompHaus
open InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitStageObservationRangeTopCat
open InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitObservables
open InfoGeometry.Canonical.RealUHFCompatibleStateObservableTopCat
open InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimit
open InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimitSymbolicLatentFlow
open InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitSymbolicLatentFlow
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Topology

abbrev compatibleCarrier := CompatibleContinuousReadoutFamily
abbrev inverseLimitCarrier := (limit readoutDiagram).carrier
abbrev compatibleFlow := scalarDilationCompatibleReadoutFamilyFlow
abbrev inverseLimitFlow := scalarDilationSymbolicLatentFlow

section CompHaus

variable [CompactSpace compatibleCarrier] [T2Space compatibleCarrier]
variable [CompactSpace inverseLimitCarrier] [T2Space inverseLimitCarrier]

noncomputable def compatibleOrbitClosureToInverseStageObservationRangeCompHausHom
    (ρ : compatibleCarrier) (n : ℕ) (X : MatStage n) :
    symbolicLatentModularOrbitClosureCompHaus compatibleFlow ρ ⟶
      stageObservationRangeCompHaus (canonicalData.map ρ) n X := by
  letI : CompactSpace
      (SymbolicLatentModularOrbitClosure compatibleFlow ρ) :=
    isCompact_iff_compactSpace.mp (compatibleFlow.isCompact_orbitClosure ρ)
  letI : CompactSpace
      (SymbolicLatentModularOrbitClosure inverseLimitFlow
        (canonicalData.map ρ)) :=
    isCompact_iff_compactSpace.mp
      (inverseLimitFlow.isCompact_orbitClosure (canonicalData.map ρ))
  letI : CompactSpace (stageObservationRange (canonicalData.map ρ) n X) :=
    isCompact_iff_compactSpace.mp
      (isCompact_range
        (orbitClosureStageObservationTopCatHom
          (canonicalData.map ρ) n X).hom.continuous)
  change CompHaus.of
      (SymbolicLatentModularOrbitClosure compatibleFlow ρ) ⟶
    CompHaus.of (stageObservationRange (canonicalData.map ρ) n X)
  exact ⟨compatibleOrbitClosureToInverseStageObservationRangeTopCatHom
    ρ n X⟩

theorem compatibleOrbitClosureToInverseStageObservationRangeCompHausHom_forget
    (ρ : compatibleCarrier) (n : ℕ) (X : MatStage n) :
    compHausToTop.map
      (compatibleOrbitClosureToInverseStageObservationRangeCompHausHom
        ρ n X) =
      compatibleOrbitClosureToInverseStageObservationRangeTopCatHom
        ρ n X := by
  rfl

theorem observationRangeEqToHom_val
    {x y : inverseLimitCarrier} (n : ℕ) (X : MatStage n)
    (h : x = y)
    (z : stageObservationRangeCompHaus x n X) :
    (ConcreteCategory.hom
      (CategoryTheory.eqToHom
        (congrArg (fun w => stageObservationRangeCompHaus w n X) h)) z).1 =
      z.1 := by
  cases h
  rfl

theorem compatibleOrbitClosureToInverseStageObservationRange_flow_square
    (ρ : compatibleCarrier) (n : ℕ) (X : MatStage n) (t : ℝ) :
    compatibleOrbitClosureToInverseStageObservationRangeCompHausHom
        ρ n X ≫
        (stageObservationRangeFlowCompHausIso
          (canonicalData.map ρ) n X t).hom =
      ((compatibleFlow.orbitClosureFlowCompHausIso ρ t).hom ≫
        compatibleOrbitClosureToInverseStageObservationRangeCompHausHom
          (compatibleFlow.act t ρ) n X) ≫
        CategoryTheory.eqToHom
          (congrArg
            (fun z => stageObservationRangeCompHaus z n X)
            (canonicalData.flow_intertwines t ρ)) := by
  apply ConcreteCategory.hom_ext
  intro y
  simp only [CategoryTheory.comp_apply]
  have hρ := canonicalData.flow_intertwines t ρ
  have htransport := observationRangeEqToHom_val n X hρ
    (compatibleOrbitClosureToInverseStageObservationRangeCompHausHom
      (compatibleFlow.act t ρ) n X
      ((compatibleFlow.orbitClosureFlowCompHausIso ρ t).hom y))
  apply Subtype.ext
  change
    ((stageObservationRangeFlowCompHausIso
      (canonicalData.map ρ) n X t).hom
      (compatibleOrbitClosureToInverseStageObservationRangeCompHausHom
        ρ n X y)).1 =
      (ConcreteCategory.hom
        (CategoryTheory.eqToHom
          (congrArg
            (fun z => stageObservationRangeCompHaus z n X) hρ))
        (compatibleOrbitClosureToInverseStageObservationRangeCompHausHom
          (compatibleFlow.act t ρ) n X
          ((compatibleFlow.orbitClosureFlowCompHausIso ρ t).hom y))).1
  rw [htransport]
  change
    Real.exp t *
        (compatibleOrbitClosureToInverseStageObservationRangeTopCatHom
          ρ n X y).1 =
      (compatibleOrbitClosureToInverseStageObservationRangeTopCatHom
        (compatibleFlow.act t ρ) n X
        ((compatibleFlow.orbitClosureFlowCompHausIso ρ t).hom y)).1
  change Real.exp t * (y.1.1 n X) =
    (compatibleFlow.act t y.1).1 n X
  have hcanon0 := canonical_stage_observation_agreement y.1 n X
  have hcanon1 := canonical_stage_observation_agreement
    (compatibleFlow.act t y.1) n X
  have hscale := inverseLimitStageEvaluation_action_scalar
    (canonicalData.map y.1) n t X
  have hscale' :
      stageObservationTopCatHom n X
          (inverseLimitFlow.act t (canonicalData.map y.1)) =
        (Real.exp t) •
          stageObservationTopCatHom n X (canonicalData.map y.1) := by
    simpa [inverseLimitFlow, scalarDilationSymbolicLatentFlow,
      stageObservationTopCatHom] using hscale
  have hρy := canonicalData.flow_intertwines t y.1
  rw [← hρy] at hscale'
  calc
    Real.exp t * (y.1.1 n X) =
        Real.exp t *
          stageObservationTopCatHom n X (canonicalData.map y.1) := by
            rw [hcanon0]
    _ = stageObservationTopCatHom n X
          (canonicalData.map (compatibleFlow.act t y.1)) := by
            simpa [smul_eq_mul] using hscale'.symm
    _ = (compatibleFlow.act t y.1).1 n X := hcanon1

end CompHaus

end InfoGeometry.Canonical.RealUHFCompatibleInverseLimitObservableRangeCompHaus

end
