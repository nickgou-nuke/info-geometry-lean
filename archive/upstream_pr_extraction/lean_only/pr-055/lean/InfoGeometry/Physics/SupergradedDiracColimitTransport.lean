import InfoGeometry.Physics.SupergradedDiracCrystalTopCatColimit

/-! Transport of a compatible pair of stage operators through the existing
two-stage `TopCat` colimit.  This is only categorical transport; it does not
assert that the operators are SUSY, spectral, or gap-preserving. -/

namespace InfoGeometry.Physics.SupergradedDiracCrystalTopCatColimit

open CategoryTheory CategoryTheory.Limits

universe u

noncomputable def stageOperatorTransportCocone
    {X0 X1 : Type u} [TopologicalSpace X0] [TopologicalSpace X1]
    (f : X0 → X1) (hf : Continuous f)
    (u0 : TopCat.of X0 ⟶ TopCat.of X0)
    (u1 : TopCat.of X1 ⟶ TopCat.of X1)
    (hcompat :
      (supergradedDiracCrystalTopCatDiagram X0 X1 f hf).map
          DiracCrystalStage.Hom.step ≫ u1 =
        u0 ≫ (supergradedDiracCrystalTopCatDiagram X0 X1 f hf).map
          DiracCrystalStage.Hom.step) :
    Cocone (supergradedDiracCrystalTopCatDiagram X0 X1 f hf) :=
  supergradedDiracCrystalTopCatCompatibleCocone f hf
    (u0 ≫ supergradedDiracCrystalTopCatInjection X0 X1 f hf .initial)
    (u1 ≫ supergradedDiracCrystalTopCatInjection X0 X1 f hf .extended) (by
      calc
        (supergradedDiracCrystalTopCatDiagram X0 X1 f hf).map
            DiracCrystalStage.Hom.step ≫
              (u1 ≫ supergradedDiracCrystalTopCatInjection X0 X1 f hf .extended) =
          (u0 ≫ (supergradedDiracCrystalTopCatDiagram X0 X1 f hf).map
            DiracCrystalStage.Hom.step) ≫
              supergradedDiracCrystalTopCatInjection X0 X1 f hf .extended := by
                simpa only [Category.assoc] using congrArg
                  (fun z => z ≫ supergradedDiracCrystalTopCatInjection X0 X1 f hf .extended)
                  hcompat
        _ = u0 ≫ supergradedDiracCrystalTopCatInjection X0 X1 f hf .initial := by
          exact congrArg
            (fun z => u0 ≫ z)
            (colimit.w (supergradedDiracCrystalTopCatDiagram X0 X1 f hf)
              DiracCrystalStage.Hom.step))

noncomputable def stageOperatorTransport
    {X0 X1 : Type u} [TopologicalSpace X0] [TopologicalSpace X1]
    (f : X0 → X1) (hf : Continuous f)
    (u0 : TopCat.of X0 ⟶ TopCat.of X0)
    (u1 : TopCat.of X1 ⟶ TopCat.of X1)
    (hcompat :
      (supergradedDiracCrystalTopCatDiagram X0 X1 f hf).map
          DiracCrystalStage.Hom.step ≫ u1 =
        u0 ≫ (supergradedDiracCrystalTopCatDiagram X0 X1 f hf).map
          DiracCrystalStage.Hom.step) :
    supergradedDiracCrystalTopCatColimit X0 X1 f hf ⟶
      supergradedDiracCrystalTopCatColimit X0 X1 f hf :=
  colimit.desc _ (stageOperatorTransportCocone f hf u0 u1 hcompat)

theorem stageOperatorTransport_initial
    {X0 X1 : Type u} [TopologicalSpace X0] [TopologicalSpace X1]
    (f : X0 → X1) (hf : Continuous f)
    (u0 : TopCat.of X0 ⟶ TopCat.of X0)
    (u1 : TopCat.of X1 ⟶ TopCat.of X1)
    (hcompat :
      (supergradedDiracCrystalTopCatDiagram X0 X1 f hf).map
          DiracCrystalStage.Hom.step ≫ u1 =
        u0 ≫ (supergradedDiracCrystalTopCatDiagram X0 X1 f hf).map
          DiracCrystalStage.Hom.step) :
    supergradedDiracCrystalTopCatInjection X0 X1 f hf .initial ≫
        stageOperatorTransport f hf u0 u1 hcompat =
      u0 ≫ supergradedDiracCrystalTopCatInjection X0 X1 f hf .initial := by
  exact colimit.ι_desc (stageOperatorTransportCocone f hf u0 u1 hcompat)
    DiracCrystalStage.initial

theorem stageOperatorTransport_extended
    {X0 X1 : Type u} [TopologicalSpace X0] [TopologicalSpace X1]
    (f : X0 → X1) (hf : Continuous f)
    (u0 : TopCat.of X0 ⟶ TopCat.of X0)
    (u1 : TopCat.of X1 ⟶ TopCat.of X1)
    (hcompat :
      (supergradedDiracCrystalTopCatDiagram X0 X1 f hf).map
          DiracCrystalStage.Hom.step ≫ u1 =
        u0 ≫ (supergradedDiracCrystalTopCatDiagram X0 X1 f hf).map
          DiracCrystalStage.Hom.step) :
    supergradedDiracCrystalTopCatInjection X0 X1 f hf .extended ≫
        stageOperatorTransport f hf u0 u1 hcompat =
      u1 ≫ supergradedDiracCrystalTopCatInjection X0 X1 f hf .extended := by
  exact colimit.ι_desc (stageOperatorTransportCocone f hf u0 u1 hcompat)
    DiracCrystalStage.extended

end InfoGeometry.Physics.SupergradedDiracCrystalTopCatColimit
