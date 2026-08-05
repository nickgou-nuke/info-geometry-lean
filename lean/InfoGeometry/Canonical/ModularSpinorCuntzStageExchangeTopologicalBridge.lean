import InfoGeometry.Canonical.ModularSpinorCuntzStageTopologicalRepresentationBridge
import InfoGeometry.Canonical.CuntzStageExchangeTopologicalColimit

namespace InfoGeometry.Canonical

open CategoryTheory
open CategoryTheory.Limits
open FilteredColimit.Native.Topological
open InfoGeometry.Canonical.CuntzStarInductiveSystem
open InfoGeometry.Canonical.CuntzStageModularFlow

noncomputable section

universe u

/-!
# Modular-spinor / Cuntz-stage exchange topological colimit bridge

This file adds the next honest node after
`ModularSpinorCuntzStageTopologicalRepresentationBridge`. The current repository already owns:

* a modular-spinor / Cuntz-stage topological representation bridge;
* a genuine Cuntz-stage exchange topological colimit (`exchangeTopologicalColimitMap`,
  `exchangeTopologicalColimitMap_involution`).

What it does not own is an analytic theorem identifying the modular-spinor
sheaf spectrum with any specific Cuntz exchange or KMS invariance.
Accordingly, this file only packages the two owner surfaces together and
re-exports the native categorical laws already proved in each.
-/

variable {E Sections BoundarySections Gr Open : Type*}
variable [AddCommGroup Sections] [Module ℝ Sections]
variable [AddCommGroup BoundarySections] [Module ℝ BoundarySections]
variable [TopologicalSpace Gr] [Category Open]
variable {J : Type u} [Category.{u, u} J]
variable {F : J ⥤ TopCat.{u}}

/-- A joint owner for the modular-spinor Cuntz-stage topological representation bridge and the
Cuntz-stage exchange topological colimit. -/
structure ModularSpinorCuntzStageExchangeTopologicalBridge
  {E Sections BoundarySections Gr Open : Type*}
  [AddCommGroup Sections] [Module ℝ Sections]
  [AddCommGroup BoundarySections] [Module ℝ BoundarySections]
  [TopologicalSpace Gr] [Category Open]
  {J : Type u} [Category.{u, u} J]
  (F : J ⥤ TopCat.{u}) where
  topologicalRepresentationBridge : ModularSpinorCuntzStageTopologicalRepresentationBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F

/-- The sheaf cover condition remains available inside the exchange topological bridge. -/
theorem modularSpinor_CuntzStageExchangeTopological_monogenicSheaf_isSheafFor
  {E Sections BoundarySections Gr Open : Type*}
  [AddCommGroup Sections] [Module ℝ Sections]
  [AddCommGroup BoundarySections] [Module ℝ BoundarySections]
  [TopologicalSpace Gr] [Category Open]
  {J : Type u} [Category.{u, u} J]
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorCuntzStageExchangeTopologicalBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F) :
    Presieve.IsSheafFor
      B.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.sheafData.sections
      B.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.sheafData.cover :=
  modularSpinor_CuntzStageTopologicalRepresentation_monogenicSheaf_isSheafFor F B.topologicalRepresentationBridge

/-- The monogenic section membership theorem remains available inside the
exchange topological bridge. -/
theorem modularSpinor_CuntzStageExchangeTopological_monogenicSection_mem
  {E Sections BoundarySections Gr Open : Type*}
  [AddCommGroup Sections] [Module ℝ Sections]
  [AddCommGroup BoundarySections] [Module ℝ BoundarySections]
  [TopologicalSpace Gr] [Category Open]
  {J : Type u} [Category.{u, u} J]
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorCuntzStageExchangeTopologicalBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F)
  (U : Open) (s : B.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.sheafData.monogenicSections U) :
    (s : B.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.sheafData.sections.obj (Opposite.op U))
      ∈ B.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.sheafData.monogenicSections U :=
  modularSpinor_CuntzStageTopologicalRepresentation_monogenicSection_mem F B.topologicalRepresentationBridge U s

/-- The boundary DN kernel theorem remains available inside the
exchange topological bridge. -/
theorem modularSpinor_CuntzStageExchangeTopological_boundary_kernel_eq_traceMonogenic
  {E Sections BoundarySections Gr Open : Type*}
  [AddCommGroup Sections] [Module ℝ Sections]
  [AddCommGroup BoundarySections] [Module ℝ BoundarySections]
  [TopologicalSpace Gr] [Category Open]
  {J : Type u} [Category.{u, u} J]
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorCuntzStageExchangeTopologicalBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F) :
    LinearMap.ker
      B.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.boundaryBridge.boundaryData.dirichletToNeumann =
      traceMonogenic B.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.boundaryBridge.boundaryData :=
  modularSpinor_CuntzStageTopologicalRepresentation_boundary_kernel_eq_traceMonogenic F B.topologicalRepresentationBridge

/-- The categorical spectrum descent map from the sheaf/spectrum bridge
remains available inside the exchange topological bridge. -/
noncomputable def modularSpinor_CuntzStageExchangeTopological_gelfandSpectrumDescend
  {E Sections BoundarySections Gr Open : Type*}
  [AddCommGroup Sections] [Module ℝ Sections]
  [AddCommGroup BoundarySections] [Module ℝ BoundarySections]
  [TopologicalSpace Gr] [Category Open]
  {J : Type u} [Category.{u, u} J]
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorCuntzStageExchangeTopologicalBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F) :
    GelfandSpectrum F ⟶ GelfandSpectrum F :=
  modularSpinor_CuntzStageTopologicalRepresentation_gelfandSpectrumDescend F B.topologicalRepresentationBridge

/-- The categorical spectrum identification from the sheaf/spectrum bridge
remains available inside the exchange topological bridge. -/
noncomputable def modularSpinor_CuntzStageExchangeTopological_gelfandSpectrumIsoTarget
  {E Sections BoundarySections Gr Open : Type*}
  [AddCommGroup Sections] [Module ℝ Sections]
  [AddCommGroup BoundarySections] [Module ℝ BoundarySections]
  [TopologicalSpace Gr] [Category Open]
  {J : Type u} [Category.{u, u} J]
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorCuntzStageExchangeTopologicalBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F) :
    GelfandSpectrum F ≅ GelfandSpectrum F :=
  modularSpinor_CuntzStageTopologicalRepresentation_gelfandSpectrumIsoTarget F B.topologicalRepresentationBridge

@[reassoc (attr := simp)]
theorem modularSpinor_CuntzStageExchangeTopological_gelfandSpectrum_stage
  {E Sections BoundarySections Gr Open : Type*}
  [AddCommGroup Sections] [Module ℝ Sections]
  [AddCommGroup BoundarySections] [Module ℝ BoundarySections]
  [TopologicalSpace Gr] [Category Open]
  {J : Type u} [Category.{u, u} J]
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorCuntzStageExchangeTopologicalBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F)
  (j : J) :
    colimit.ι F j ≫
      modularSpinor_CuntzStageExchangeTopological_gelfandSpectrumDescend F B =
      colimit.ι F j :=
  by
  dsimp only [modularSpinor_CuntzStageExchangeTopological_gelfandSpectrumDescend] at *
  exact modularSpinor_CuntzStageTopologicalRepresentation_gelfandSpectrum_stage F B.topologicalRepresentationBridge j

/-- The filtered topological direct colimit stage maps remain available
inside the exchange topological bridge. -/
noncomputable def modularSpinor_CuntzStageExchangeTopological_stageInjection
  {E Sections BoundarySections Gr Open : Type*}
  [AddCommGroup Sections] [Module ℝ Sections]
  [AddCommGroup BoundarySections] [Module ℝ BoundarySections]
  [TopologicalSpace Gr] [Category Open]
  {J : Type u} [Category.{u, u} J]
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorCuntzStageExchangeTopologicalBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F)
  (j : J) : B.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.stageDiagram.obj j ⟶ colimit B.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.stageDiagram :=
  modularSpinor_CuntzStageTopologicalRepresentation_stageInjection F B.topologicalRepresentationBridge j

/-- Naturality of the filtered colimit stage maps remains available
inside the exchange topological bridge. -/
theorem modularSpinor_CuntzStageExchangeTopological_stageInjection_naturality
  {E Sections BoundarySections Gr Open : Type*}
  [AddCommGroup Sections] [Module ℝ Sections]
  [AddCommGroup BoundarySections] [Module ℝ BoundarySections]
  [TopologicalSpace Gr] [Category Open]
  {J : Type u} [Category.{u, u} J]
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorCuntzStageExchangeTopologicalBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F)
  {j j' : J} (f : j ⟶ j') :
    B.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.stageDiagram.map f ≫
      modularSpinor_CuntzStageExchangeTopological_stageInjection F B j' =
      modularSpinor_CuntzStageExchangeTopological_stageInjection F B j :=
  by
  dsimp only [modularSpinor_CuntzStageExchangeTopological_stageInjection] at *
  exact modularSpinor_CuntzStageTopologicalRepresentation_stageInjection_naturality F B.topologicalRepresentationBridge f

/-- Modular-spinor transport still preserves the canonical three-form
inside the full exchange topological bridge. -/
theorem modularSpinor_CuntzStageExchangeTopological_transport_preserves_threeForm
  {E Sections BoundarySections Gr Open : Type*}
  [AddCommGroup Sections] [Module ℝ Sections]
  [AddCommGroup BoundarySections] [Module ℝ BoundarySections]
  [TopologicalSpace Gr] [Category Open]
  {J : Type u} [Category.{u, u} J]
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorCuntzStageExchangeTopologicalBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F)
  (path : List E) (x y z : ModularSpinorCarrier) :
    canonicalSplitG2ThreeFormValue
        ((modularSpinorTransport
          B.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.boundaryBridge.connection path) x)
        ((modularSpinorTransport
          B.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.boundaryBridge.connection path) y)
        ((modularSpinorTransport
          B.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.boundaryBridge.connection path) z) =
      canonicalSplitG2ThreeFormValue x y z := by
  have h := modularSpinor_CuntzStageTopologicalRepresentation_transport_preserves_threeForm F B.topologicalRepresentationBridge path x y z
  simp_all [modularSpinorTransport]
  <;>
  exact h

end

end InfoGeometry.Canonical
