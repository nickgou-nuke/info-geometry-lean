import InfoGeometry.Canonical.RealUHFCompatibleReadoutObservableOrbitClosureCompHaus
import InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitDynamics
import InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitStageObservationTopCat

/-!
# Explicit comparison of the two inverse-limit carriers

The compatible continuous-readout carrier and the existing inverse-limit
stage-observation carrier are different types.  This owner introduces their
comparison only as explicit continuous data and records the required flow
intertwining square.  No canonical identification is inferred.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealUHFCompatibleInverseLimitFlowComparison

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimit
open InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimitSymbolicLatentFlow
open InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimit
open InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitDynamics
open InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitObservables
open InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitSymbolicLatentFlow
open InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitStageObservationTopCat
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Topology

abbrev compatibleCarrier := CompatibleContinuousReadoutFamily
abbrev inverseLimitCarrier := (limit readoutDiagram).carrier
abbrev compatibleFlow := scalarDilationCompatibleReadoutFamilyFlow
abbrev inverseLimitFlow := scalarDilationSymbolicLatentFlow

structure Data where
  map : compatibleCarrier → inverseLimitCarrier
  continuous_map : Continuous map
  flow_intertwines : ∀ (t : ℝ) (ρ : compatibleCarrier),
    map (compatibleFlow.act t ρ) =
      inverseLimitFlow.act t (map ρ)

structure StageObservationData where
  base : Data
  stage_observation_agrees :
    ∀ (ρ : compatibleCarrier) (n : ℕ) (X : MatStage n),
      stageObservationTopCatHom n X (base.map ρ) = ρ.1 n X

theorem stage_observation_agreement
    (D : StageObservationData) (ρ : compatibleCarrier)
    (n : ℕ) (X : MatStage n) :
    stageObservationTopCatHom n X (D.base.map ρ) = ρ.1 n X :=
  D.stage_observation_agrees ρ n X

noncomputable def canonicalData : Data where
  map := compatibleReadoutInverseLimitIso.hom
  continuous_map := compatibleReadoutInverseLimitIso.hom.hom.continuous
  flow_intertwines := by
    intro t ρ
    have h := congrArg (fun f => f ρ)
      (scalarDilationReadoutInverseLimitAction_transport t)
    simpa [compatibleFlow, inverseLimitFlow,
      scalarDilationCompatibleReadoutFamilyFlow,
      scalarDilationSymbolicLatentFlow, TopCat.comp_app] using h

theorem canonical_stage_observation_agreement
    (ρ : compatibleCarrier) (n : ℕ) (X : MatStage n) :
    stageObservationTopCatHom n X (canonicalData.map ρ) = ρ.1 n X := by
  have h := congrArg (fun f => f ρ)
    (compatibleReadoutInverseLimitIso_coordinateEvaluation n X)
  simpa [canonicalData, stageObservationTopCatHom, TopCat.comp_app] using h.symm

noncomputable def canonicalStageObservationData : StageObservationData where
  base := canonicalData
  stage_observation_agrees := canonical_stage_observation_agreement

noncomputable def canonicalOrbitClosureMap (ρ : compatibleCarrier) :
    SymbolicLatentModularOrbitClosure compatibleFlow ρ →
      SymbolicLatentModularOrbitClosure inverseLimitFlow
        (canonicalData.map ρ) :=
  fun y => ⟨canonicalData.map y.1, by
    apply map_mem_closure canonicalData.continuous_map y.2
    intro z hz
    rcases hz with ⟨t, rfl⟩
    exact ⟨t, (canonicalData.flow_intertwines t ρ).symm⟩⟩

theorem canonicalOrbitClosureMap_continuous (ρ : compatibleCarrier) :
    Continuous (canonicalOrbitClosureMap ρ) := by
  exact (canonicalData.continuous_map.comp continuous_subtype_val).subtype_mk
    (fun y => by
      apply map_mem_closure canonicalData.continuous_map y.2
      intro z hz
      rcases hz with ⟨t, rfl⟩
      exact ⟨t, (canonicalData.flow_intertwines t ρ).symm⟩)

theorem canonicalOrbitClosureMap_inclusion (ρ : compatibleCarrier)
    (y : SymbolicLatentModularOrbitClosure compatibleFlow ρ) :
    (canonicalOrbitClosureMap ρ y).1 = canonicalData.map y.1 := rfl

noncomputable def canonicalOrbitClosureTopCatHom (ρ : compatibleCarrier) :
    TopCat.of (SymbolicLatentModularOrbitClosure compatibleFlow ρ) ⟶
      TopCat.of (SymbolicLatentModularOrbitClosure inverseLimitFlow
        (canonicalData.map ρ)) :=
  TopCat.ofHom
    { toFun := canonicalOrbitClosureMap ρ
      continuous_toFun := canonicalOrbitClosureMap_continuous ρ }

theorem canonicalOrbitClosureTopCatHom_apply (ρ : compatibleCarrier)
    (y : SymbolicLatentModularOrbitClosure compatibleFlow ρ) :
    canonicalOrbitClosureTopCatHom ρ y = canonicalOrbitClosureMap ρ y := rfl

noncomputable def toTopCatHom (D : Data) :
    TopCat.of compatibleCarrier ⟶ TopCat.of inverseLimitCarrier :=
  TopCat.ofHom
    { toFun := D.map
      continuous_toFun := D.continuous_map }

theorem toTopCatHom_apply (D : Data) (ρ : compatibleCarrier) :
    toTopCatHom D ρ = D.map ρ := rfl

theorem canonicalOrbitClosure_inclusion_square (ρ : compatibleCarrier) :
    canonicalOrbitClosureTopCatHom ρ ≫
        inverseLimitFlow.orbitClosureInclusionTopCatHom
          (canonicalData.map ρ) =
      compatibleFlow.orbitClosureInclusionTopCatHom ρ ≫
        toTopCatHom canonicalData := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro y
  rfl

theorem canonicalOrbitClosure_flow_naturality
    [T2Space inverseLimitCarrier]
    (ρ : compatibleCarrier) (t : ℝ)
    (y : SymbolicLatentModularOrbitClosure compatibleFlow ρ) :
    (canonicalOrbitClosureMap (compatibleFlow.act t ρ)
      (compatibleFlow.orbitClosureFlowHomeomorph ρ t y)).1 =
      (inverseLimitFlow.orbitClosureFlowHomeomorph
        (canonicalData.map ρ) t (canonicalOrbitClosureMap ρ y)).1 := by
  change canonicalData.map (compatibleFlow.act t y.1) =
    inverseLimitFlow.act t (canonicalData.map y.1)
  exact canonicalData.flow_intertwines t y.1

section CompHaus

variable [CompactSpace compatibleCarrier] [T2Space compatibleCarrier]
variable [CompactSpace inverseLimitCarrier] [T2Space inverseLimitCarrier]

noncomputable def canonicalOrbitClosureCompHausHom (ρ : compatibleCarrier) :
    symbolicLatentModularOrbitClosureCompHaus compatibleFlow ρ ⟶
      symbolicLatentModularOrbitClosureCompHaus inverseLimitFlow
        (canonicalData.map ρ) := by
  letI : CompactSpace
      (SymbolicLatentModularOrbitClosure compatibleFlow ρ) :=
    isCompact_iff_compactSpace.mp
      (compatibleFlow.isCompact_orbitClosure ρ)
  letI : CompactSpace
      (SymbolicLatentModularOrbitClosure inverseLimitFlow
        (canonicalData.map ρ)) :=
    isCompact_iff_compactSpace.mp
      (inverseLimitFlow.isCompact_orbitClosure (canonicalData.map ρ))
  change CompHaus.of
      (SymbolicLatentModularOrbitClosure compatibleFlow ρ) ⟶
    CompHaus.of
      (SymbolicLatentModularOrbitClosure inverseLimitFlow
        (canonicalData.map ρ))
  exact ⟨canonicalOrbitClosureTopCatHom ρ⟩

theorem canonicalOrbitClosureCompHausHom_forget (ρ : compatibleCarrier) :
    compHausToTop.map (canonicalOrbitClosureCompHausHom ρ) =
      canonicalOrbitClosureTopCatHom ρ := by
  letI : CompactSpace
      (SymbolicLatentModularOrbitClosure compatibleFlow ρ) :=
    isCompact_iff_compactSpace.mp
      (compatibleFlow.isCompact_orbitClosure ρ)
  letI : CompactSpace
      (SymbolicLatentModularOrbitClosure inverseLimitFlow
        (canonicalData.map ρ)) :=
    isCompact_iff_compactSpace.mp
      (inverseLimitFlow.isCompact_orbitClosure (canonicalData.map ρ))
  change compHausToTop.map
      (⟨canonicalOrbitClosureTopCatHom ρ⟩ :
        CompHaus.of
            (SymbolicLatentModularOrbitClosure compatibleFlow ρ) ⟶
          CompHaus.of
            (SymbolicLatentModularOrbitClosure inverseLimitFlow
              (canonicalData.map ρ))) =
    canonicalOrbitClosureTopCatHom ρ
  rfl

theorem orbitClosureEqToHom_val
    {x y : inverseLimitCarrier} (h : x = y)
    (z : SymbolicLatentModularOrbitClosure inverseLimitFlow x) :
    (ConcreteCategory.hom
      (CategoryTheory.eqToHom
        (congrArg
          (fun w => symbolicLatentModularOrbitClosureCompHaus
            inverseLimitFlow w) h)) z).1 = z.1 := by
  cases h
  rfl

theorem canonicalOrbitClosureCompHaus_flow_square
    (ρ : compatibleCarrier) (t : ℝ) :
    canonicalOrbitClosureCompHausHom ρ ≫
        (inverseLimitFlow.orbitClosureFlowCompHausIso
          (canonicalData.map ρ) t).hom =
      ((compatibleFlow.orbitClosureFlowCompHausIso ρ t).hom ≫
        canonicalOrbitClosureCompHausHom (compatibleFlow.act t ρ)) ≫
        CategoryTheory.eqToHom
          (congrArg
            (fun z => symbolicLatentModularOrbitClosureCompHaus
              inverseLimitFlow z)
            (canonicalData.flow_intertwines t ρ)) := by
  apply ConcreteCategory.hom_ext
  intro y
  simp only [CategoryTheory.comp_apply]
  have hρ := canonicalData.flow_intertwines t ρ
  have htransport :=
    orbitClosureEqToHom_val hρ
      (canonicalOrbitClosureMap (compatibleFlow.act t ρ)
        ((compatibleFlow.orbitClosureFlowCompHausIso ρ t).hom y))
  apply Subtype.ext
  change inverseLimitFlow.act t (canonicalData.map y.1) =
    ((ConcreteCategory.hom
      (CategoryTheory.eqToHom
        (congrArg
          (fun z => symbolicLatentModularOrbitClosureCompHaus
            inverseLimitFlow z) hρ)))
      (canonicalOrbitClosureMap (compatibleFlow.act t ρ)
        ((compatibleFlow.orbitClosureFlowCompHausIso ρ t).hom y))).1
  rw [htransport]
  change inverseLimitFlow.act t (canonicalData.map y.1) =
    canonicalData.map (compatibleFlow.act t y.1)
  exact (canonicalData.flow_intertwines t y.1).symm

end CompHaus

theorem flow_intertwining_square (D : Data) (t : ℝ) :
    toTopCatHom D ≫ inverseLimitFlow.actTopCatHom t =
      compatibleFlow.actTopCatHom t ≫ toTopCatHom D := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro ρ
  simpa [toTopCatHom] using (D.flow_intertwines t ρ).symm

end InfoGeometry.Canonical.RealUHFCompatibleInverseLimitFlowComparison

end
