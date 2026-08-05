import InfoGeometry.Canonical.ModularSpinorFilteredColimitBridge
import InfoGeometry.Canonical.CuntzStageModularFlowColimit

namespace InfoGeometry.Canonical

open CategoryTheory
open CategoryTheory.Limits
open FilteredColimit.Native.Topological

noncomputable section

universe u

/-!
# Modular-spinor / Cuntz-stage modular flow colimit bridge

This file adds the next honest node after
`ModularSpinorFilteredColimitBridge`. The current repository already owns:

* a filtered topological colimit bridge over the modular-spinor sheaf/spectrum;
* a genuine Cuntz-stage modular flow colimit owner (`BoundedModularKMSBridge` is
  exposed via `CuntzStageModularFlowColimitReadout`).

What it does not own is an analytic theorem identifying the modular-spinor
sheaf spectrum with any specific Cuntz modular flow stage or KMS invariance.
Accordingly, this file only packages the two owner surfaces together and
re-exports the native categorical laws already proved in each.
-/

/-- A joint owner for the modular-spinor filtered colimit bridge and the
Cuntz-stage modular flow colimit. -/
abbrev ModularSpinorCuntzStageColimitBridge
  {E Sections BoundarySections Gr Open : Type*}
  [AddCommGroup Sections] [Module ℝ Sections]
  [AddCommGroup BoundarySections] [Module ℝ BoundarySections]
  [TopologicalSpace Gr] [Category Open]
  {J : Type u} [Category.{u, u} J]
  (F : J ⥤ TopCat.{u}) :=
  ModularSpinorFilteredColimitBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F

namespace ModularSpinorCuntzStageColimitBridge

/-- Compatibility projection for the former one-field wrapper. -/
abbrev filteredColimitBridge
  {E Sections BoundarySections Gr Open : Type*}
  [AddCommGroup Sections] [Module ℝ Sections]
  [AddCommGroup BoundarySections] [Module ℝ BoundarySections]
  [TopologicalSpace Gr] [Category Open]
  {J : Type u} [Category.{u, u} J]
  {F : J ⥤ TopCat.{u}}
  (B : ModularSpinorCuntzStageColimitBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F) := B

end ModularSpinorCuntzStageColimitBridge

/-- The sheaf cover condition remains available inside the Cuntz-stage colimit bridge. -/
theorem modularSpinor_CuntzStageColimit_monogenicSheaf_isSheafFor
  {E Sections BoundarySections Gr Open : Type*}
  [AddCommGroup Sections] [Module ℝ Sections]
  [AddCommGroup BoundarySections] [Module ℝ BoundarySections]
  [TopologicalSpace Gr] [Category Open]
  {J : Type u} [Category.{u, u} J]
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorCuntzStageColimitBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F) :
    Presieve.IsSheafFor
      B.filteredColimitBridge.spectrumBridge.sheafData.sections
      B.filteredColimitBridge.spectrumBridge.sheafData.cover :=
  modularSpinor_filteredColimit_monogenicSheaf_isSheafFor F B.filteredColimitBridge

/-- The monogenic section membership theorem remains available inside the
Cuntz-stage colimit bridge. -/
theorem modularSpinor_CuntzStageColimit_monogenicSection_mem
  {E Sections BoundarySections Gr Open : Type*}
  [AddCommGroup Sections] [Module ℝ Sections]
  [AddCommGroup BoundarySections] [Module ℝ BoundarySections]
  [TopologicalSpace Gr] [Category Open]
  {J : Type u} [Category.{u, u} J]
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorCuntzStageColimitBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F)
  (U : Open) (s : B.filteredColimitBridge.spectrumBridge.sheafData.monogenicSections U) :
    (s : B.filteredColimitBridge.spectrumBridge.sheafData.sections.obj (Opposite.op U))
      ∈ B.filteredColimitBridge.spectrumBridge.sheafData.monogenicSections U :=
  modularSpinor_filteredColimit_monogenicSection_mem F B.filteredColimitBridge U s

/-- The boundary DN kernel theorem remains available inside the
Cuntz-stage colimit bridge. -/
theorem modularSpinor_CuntzStageColimit_boundary_kernel_eq_traceMonogenic
  {E Sections BoundarySections Gr Open : Type*}
  [AddCommGroup Sections] [Module ℝ Sections]
  [AddCommGroup BoundarySections] [Module ℝ BoundarySections]
  [TopologicalSpace Gr] [Category Open]
  {J : Type u} [Category.{u, u} J]
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorCuntzStageColimitBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F) :
    LinearMap.ker
      B.filteredColimitBridge.spectrumBridge.boundaryBridge.boundaryData.dirichletToNeumann =
      traceMonogenic B.filteredColimitBridge.spectrumBridge.boundaryBridge.boundaryData :=
  modularSpinor_filteredColimit_boundary_kernel_eq_traceMonogenic F B.filteredColimitBridge

/-- The categorical spectrum descent map from the sheaf/spectrum bridge
remains available inside the Cuntz-stage colimit bridge. -/
noncomputable def modularSpinor_CuntzStageColimit_gelfandSpectrumDescend
  {E Sections BoundarySections Gr Open : Type*}
  [AddCommGroup Sections] [Module ℝ Sections]
  [AddCommGroup BoundarySections] [Module ℝ BoundarySections]
  [TopologicalSpace Gr] [Category Open]
  {J : Type u} [Category.{u, u} J]
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorCuntzStageColimitBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F) :
    GelfandSpectrum F ⟶ GelfandSpectrum F :=
  modularSpinor_filteredColimit_gelfandSpectrumDescend F B.filteredColimitBridge

/-- The categorical spectrum identification from the sheaf/spectrum bridge
remains available inside the Cuntz-stage colimit bridge. -/
noncomputable def modularSpinor_CuntzStageColimit_gelfandSpectrumIsoTarget
  {E Sections BoundarySections Gr Open : Type*}
  [AddCommGroup Sections] [Module ℝ Sections]
  [AddCommGroup BoundarySections] [Module ℝ BoundarySections]
  [TopologicalSpace Gr] [Category Open]
  {J : Type u} [Category.{u, u} J]
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorCuntzStageColimitBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F) :
    GelfandSpectrum F ≅ GelfandSpectrum F :=
  modularSpinor_filteredColimit_gelfandSpectrumIsoTarget F B.filteredColimitBridge

@[reassoc (attr := simp)]
theorem modularSpinor_CuntzStageColimit_gelfandSpectrum_stage
  {E Sections BoundarySections Gr Open : Type*}
  [AddCommGroup Sections] [Module ℝ Sections]
  [AddCommGroup BoundarySections] [Module ℝ BoundarySections]
  [TopologicalSpace Gr] [Category Open]
  {J : Type u} [Category.{u, u} J]
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorCuntzStageColimitBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F)
  (j : J) :
    colimit.ι F j ≫
      modularSpinor_CuntzStageColimit_gelfandSpectrumDescend F B =
      colimit.ι F j :=
  by
  dsimp only [modularSpinor_CuntzStageColimit_gelfandSpectrumDescend] at *
  exact modularSpinor_filteredColimit_gelfandSpectrum_stage F B.filteredColimitBridge j

/-- The filtered topological direct colimit stage maps remain available
inside the Cuntz-stage colimit bridge. -/
noncomputable def modularSpinor_CuntzStageColimit_stageInjection
  {E Sections BoundarySections Gr Open : Type*}
  [AddCommGroup Sections] [Module ℝ Sections]
  [AddCommGroup BoundarySections] [Module ℝ BoundarySections]
  [TopologicalSpace Gr] [Category Open]
  {J : Type u} [Category.{u, u} J]
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorCuntzStageColimitBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F)
  (j : J) : B.filteredColimitBridge.stageDiagram.obj j ⟶ colimit B.filteredColimitBridge.stageDiagram :=
  modularSpinor_filteredColimit_stageInjection F B.filteredColimitBridge j

/-- Naturality of the filtered colimit stage maps remains available
inside the Cuntz-stage colimit bridge. -/
theorem modularSpinor_CuntzStageColimit_stageInjection_naturality
  {E Sections BoundarySections Gr Open : Type*}
  [AddCommGroup Sections] [Module ℝ Sections]
  [AddCommGroup BoundarySections] [Module ℝ BoundarySections]
  [TopologicalSpace Gr] [Category Open]
  {J : Type u} [Category.{u, u} J]
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorCuntzStageColimitBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F)
  {j j' : J} (f : j ⟶ j') :
    B.filteredColimitBridge.stageDiagram.map f ≫
      modularSpinor_CuntzStageColimit_stageInjection F B j' =
      modularSpinor_CuntzStageColimit_stageInjection F B j :=
  by
  dsimp only [modularSpinor_CuntzStageColimit_stageInjection] at *
  exact modularSpinor_filteredColimit_stageInjection_naturality F B.filteredColimitBridge f

/-- Modular-spinor transport still preserves the canonical three-form
inside the full Cuntz-stage colimit bridge. -/
theorem modularSpinor_CuntzStageColimit_transport_preserves_threeForm
  {E Sections BoundarySections Gr Open : Type*}
  [AddCommGroup Sections] [Module ℝ Sections]
  [AddCommGroup BoundarySections] [Module ℝ BoundarySections]
  [TopologicalSpace Gr] [Category Open]
  {J : Type u} [Category.{u, u} J]
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorCuntzStageColimitBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F)
  (path : List E) (x y z : ModularSpinorCarrier) :
    canonicalSplitG2ThreeFormValue
        ((modularSpinorTransport
          B.filteredColimitBridge.spectrumBridge.boundaryBridge.connection path) x)
        ((modularSpinorTransport
          B.filteredColimitBridge.spectrumBridge.boundaryBridge.connection path) y)
        ((modularSpinorTransport
          B.filteredColimitBridge.spectrumBridge.boundaryBridge.connection path) z) =
      canonicalSplitG2ThreeFormValue x y z := by
  have h := modularSpinor_filteredColimit_transport_preserves_threeForm F B.filteredColimitBridge path x y z
  simp_all [modularSpinorTransport]
  <;>
  exact h

end

end InfoGeometry.Canonical
