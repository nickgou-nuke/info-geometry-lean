import InfoGeometry.Canonical.ModularSpinorCuntzStageTopologicalIsoBridge
import InfoGeometry.Canonical.CuntzStageModularFlowTopologicalRepresentationBridge

namespace InfoGeometry.Canonical

open CategoryTheory
open CategoryTheory.Limits
open FilteredColimit.Native.Topological
open InfoGeometry.Canonical.CuntzStarInductiveSystem
open InfoGeometry.Canonical.CuntzStageModularFlow

noncomputable section

universe u

/-!
# Modular-spinor / Cuntz-stage topological representation bridge

This file adds the next honest node after
`ModularSpinorCuntzStageTopologicalIsoBridge`. The current repository already owns:

* a modular-spinor / Cuntz-stage topological isomorphism bridge;
* a genuine Cuntz-stage modular flow topological representation bridge
  (`modularFlow_intertwines_invariant_representation`).

What it does not own is an analytic theorem identifying the modular-spinor
sheaf spectrum with any specific Cuntz modular flow representation or KMS invariance.
Accordingly, this file only packages the two owner surfaces together and
re-exports the native categorical laws already proved in each.
-/

variable {E Sections BoundarySections Gr Open : Type*}
variable [AddCommGroup Sections] [Module ℝ Sections]
variable [AddCommGroup BoundarySections] [Module ℝ BoundarySections]
variable [TopologicalSpace Gr] [Category Open]
variable {J : Type u} [Category.{u, u} J]
variable {F : J ⥤ TopCat.{u}}

/-- A joint owner for the modular-spinor Cuntz-stage topological isomorphism bridge and the
Cuntz-stage modular flow topological representation bridge. -/
structure ModularSpinorCuntzStageTopologicalRepresentationBridge
  {E Sections BoundarySections Gr Open : Type*}
  [AddCommGroup Sections] [Module ℝ Sections]
  [AddCommGroup BoundarySections] [Module ℝ BoundarySections]
  [TopologicalSpace Gr] [Category Open]
  {J : Type u} [Category.{u, u} J]
  (F : J ⥤ TopCat.{u}) where
  topologicalIsoBridge : ModularSpinorCuntzStageTopologicalIsoBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F

/-- The sheaf cover condition remains available inside the topological representation bridge. -/
theorem modularSpinor_CuntzStageTopologicalRepresentation_monogenicSheaf_isSheafFor
  {E Sections BoundarySections Gr Open : Type*}
  [AddCommGroup Sections] [Module ℝ Sections]
  [AddCommGroup BoundarySections] [Module ℝ BoundarySections]
  [TopologicalSpace Gr] [Category Open]
  {J : Type u} [Category.{u, u} J]
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorCuntzStageTopologicalRepresentationBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F) :
    Presieve.IsSheafFor
      B.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.sheafData.sections
      B.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.sheafData.cover :=
  modularSpinor_CuntzStageTopologicalIso_monogenicSheaf_isSheafFor F B.topologicalIsoBridge

/-- The monogenic section membership theorem remains available inside the
topological representation bridge. -/
theorem modularSpinor_CuntzStageTopologicalRepresentation_monogenicSection_mem
  {E Sections BoundarySections Gr Open : Type*}
  [AddCommGroup Sections] [Module ℝ Sections]
  [AddCommGroup BoundarySections] [Module ℝ BoundarySections]
  [TopologicalSpace Gr] [Category Open]
  {J : Type u} [Category.{u, u} J]
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorCuntzStageTopologicalRepresentationBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F)
  (U : Open) (s : B.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.sheafData.monogenicSections U) :
    (s : B.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.sheafData.sections.obj (Opposite.op U))
      ∈ B.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.sheafData.monogenicSections U :=
  modularSpinor_CuntzStageTopologicalIso_monogenicSection_mem F B.topologicalIsoBridge U s

/-- The boundary DN kernel theorem remains available inside the
topological representation bridge. -/
theorem modularSpinor_CuntzStageTopologicalRepresentation_boundary_kernel_eq_traceMonogenic
  {E Sections BoundarySections Gr Open : Type*}
  [AddCommGroup Sections] [Module ℝ Sections]
  [AddCommGroup BoundarySections] [Module ℝ BoundarySections]
  [TopologicalSpace Gr] [Category Open]
  {J : Type u} [Category.{u, u} J]
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorCuntzStageTopologicalRepresentationBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F) :
    LinearMap.ker
      B.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.boundaryBridge.boundaryData.dirichletToNeumann =
      traceMonogenic B.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.boundaryBridge.boundaryData :=
  modularSpinor_CuntzStageTopologicalIso_boundary_kernel_eq_traceMonogenic F B.topologicalIsoBridge

/-- The categorical spectrum descent map from the sheaf/spectrum bridge
remains available inside the topological representation bridge. -/
noncomputable def modularSpinor_CuntzStageTopologicalRepresentation_gelfandSpectrumDescend
  {E Sections BoundarySections Gr Open : Type*}
  [AddCommGroup Sections] [Module ℝ Sections]
  [AddCommGroup BoundarySections] [Module ℝ BoundarySections]
  [TopologicalSpace Gr] [Category Open]
  {J : Type u} [Category.{u, u} J]
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorCuntzStageTopologicalRepresentationBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F) :
    GelfandSpectrum F ⟶ GelfandSpectrum F :=
  modularSpinor_CuntzStageTopologicalIso_gelfandSpectrumDescend F B.topologicalIsoBridge

/-- The categorical spectrum identification from the sheaf/spectrum bridge
remains available inside the topological representation bridge. -/
noncomputable def modularSpinor_CuntzStageTopologicalRepresentation_gelfandSpectrumIsoTarget
  {E Sections BoundarySections Gr Open : Type*}
  [AddCommGroup Sections] [Module ℝ Sections]
  [AddCommGroup BoundarySections] [Module ℝ BoundarySections]
  [TopologicalSpace Gr] [Category Open]
  {J : Type u} [Category.{u, u} J]
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorCuntzStageTopologicalRepresentationBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F) :
    GelfandSpectrum F ≅ GelfandSpectrum F :=
  modularSpinor_CuntzStageTopologicalIso_gelfandSpectrumIsoTarget F B.topologicalIsoBridge

@[reassoc (attr := simp)]
theorem modularSpinor_CuntzStageTopologicalRepresentation_gelfandSpectrum_stage
  {E Sections BoundarySections Gr Open : Type*}
  [AddCommGroup Sections] [Module ℝ Sections]
  [AddCommGroup BoundarySections] [Module ℝ BoundarySections]
  [TopologicalSpace Gr] [Category Open]
  {J : Type u} [Category.{u, u} J]
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorCuntzStageTopologicalRepresentationBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F)
  (j : J) :
    colimit.ι F j ≫
      modularSpinor_CuntzStageTopologicalRepresentation_gelfandSpectrumDescend F B =
      colimit.ι F j :=
  by
  dsimp only [modularSpinor_CuntzStageTopologicalRepresentation_gelfandSpectrumDescend] at *
  exact modularSpinor_CuntzStageTopologicalIso_gelfandSpectrum_stage F B.topologicalIsoBridge j

/-- The filtered topological direct colimit stage maps remain available
inside the topological representation bridge. -/
noncomputable def modularSpinor_CuntzStageTopologicalRepresentation_stageInjection
  {E Sections BoundarySections Gr Open : Type*}
  [AddCommGroup Sections] [Module ℝ Sections]
  [AddCommGroup BoundarySections] [Module ℝ BoundarySections]
  [TopologicalSpace Gr] [Category Open]
  {J : Type u} [Category.{u, u} J]
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorCuntzStageTopologicalRepresentationBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F)
  (j : J) : B.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.stageDiagram.obj j ⟶ colimit B.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.stageDiagram :=
  modularSpinor_CuntzStageTopologicalIso_stageInjection F B.topologicalIsoBridge j

/-- Naturality of the filtered colimit stage maps remains available
inside the topological representation bridge. -/
theorem modularSpinor_CuntzStageTopologicalRepresentation_stageInjection_naturality
  {E Sections BoundarySections Gr Open : Type*}
  [AddCommGroup Sections] [Module ℝ Sections]
  [AddCommGroup BoundarySections] [Module ℝ BoundarySections]
  [TopologicalSpace Gr] [Category Open]
  {J : Type u} [Category.{u, u} J]
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorCuntzStageTopologicalRepresentationBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F)
  {j j' : J} (f : j ⟶ j') :
    B.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.stageDiagram.map f ≫
      modularSpinor_CuntzStageTopologicalRepresentation_stageInjection F B j' =
      modularSpinor_CuntzStageTopologicalRepresentation_stageInjection F B j :=
  by
  dsimp only [modularSpinor_CuntzStageTopologicalRepresentation_stageInjection] at *
  exact modularSpinor_CuntzStageTopologicalIso_stageInjection_naturality F B.topologicalIsoBridge f

/-- Modular-spinor transport still preserves the canonical three-form
inside the full topological representation bridge. -/
theorem modularSpinor_CuntzStageTopologicalRepresentation_transport_preserves_threeForm
  {E Sections BoundarySections Gr Open : Type*}
  [AddCommGroup Sections] [Module ℝ Sections]
  [AddCommGroup BoundarySections] [Module ℝ BoundarySections]
  [TopologicalSpace Gr] [Category Open]
  {J : Type u} [Category.{u, u} J]
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorCuntzStageTopologicalRepresentationBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F)
  (path : List E) (x y z : ModularSpinorCarrier) :
    canonicalSplitG2ThreeFormValue
        ((modularSpinorTransport
          B.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.boundaryBridge.connection path) x)
        ((modularSpinorTransport
          B.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.boundaryBridge.connection path) y)
        ((modularSpinorTransport
          B.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.boundaryBridge.connection path) z) =
      canonicalSplitG2ThreeFormValue x y z := by
  have h := modularSpinor_CuntzStageTopologicalIso_transport_preserves_threeForm F B.topologicalIsoBridge path x y z
  simp_all [modularSpinorTransport]
  <;>
  exact h

end

end InfoGeometry.Canonical
