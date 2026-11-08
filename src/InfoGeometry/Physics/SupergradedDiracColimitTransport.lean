import InfoGeometry.Physics.SupergradedDiracCrystalTopCatColimit
import InfoGeometry.Algebra.FiniteSpinAlgebra

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
      let F := supergradedDiracCrystalTopCatDiagram X0 X1 f hf
      let u₀ : F.obj .initial ⟶ F.obj .initial := u0
      let u₁ : F.obj .extended ⟶ F.obj .extended := u1
      let ι₀ : F.obj .initial ⟶ supergradedDiracCrystalTopCatColimit X0 X1 f hf :=
        supergradedDiracCrystalTopCatInjection X0 X1 f hf .initial
      let ι₁ : F.obj .extended ⟶ supergradedDiracCrystalTopCatColimit X0 X1 f hf :=
        supergradedDiracCrystalTopCatInjection X0 X1 f hf .extended
      have hc : F.map DiracCrystalStage.Hom.step ≫ u₁ = u₀ ≫
          F.map DiracCrystalStage.Hom.step := hcompat
      have hw : F.map DiracCrystalStage.Hom.step ≫ ι₁ = ι₀ :=
        colimit.w F DiracCrystalStage.Hom.step
      change F.map DiracCrystalStage.Hom.step ≫ (u₁ ≫ ι₁) = u₀ ≫ ι₀
      calc
        F.map DiracCrystalStage.Hom.step ≫ (u₁ ≫ ι₁) =
            (F.map DiracCrystalStage.Hom.step ≫ u₁) ≫ ι₁ :=
          (Category.assoc _ _ _).symm
        _ = (u₀ ≫ F.map DiracCrystalStage.Hom.step) ≫ ι₁ :=
          congrArg (fun g => g ≫ ι₁) hc
        _ = u₀ ≫ ι₀ := by
          calc
            (u₀ ≫ F.map DiracCrystalStage.Hom.step) ≫ ι₁ =
                u₀ ≫ (F.map DiracCrystalStage.Hom.step ≫ ι₁) :=
              Category.assoc _ _ _
            _ = u₀ ≫ ι₀ := congrArg (fun g => u₀ ≫ g) hw)

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
