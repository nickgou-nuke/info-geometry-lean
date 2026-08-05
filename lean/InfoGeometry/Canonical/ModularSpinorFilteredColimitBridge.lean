import InfoGeometry.Canonical.ModularSpinorGrassmannianSheafBridge
import InfoGeometry.Canonical.FilteredTopologicalDirectInverseColimit

namespace InfoGeometry.Canonical

open CategoryTheory
open CategoryTheory.Limits
open FilteredColimit.Native.Topological

noncomputable section

universe u

/-!
# Modular-spinor / filtered topological colimit bridge

This file adds the next honest node after
`ModularSpinorGrassmannianSheafBridge`. The current repository already owns:

* a sheaf/spectrum bridge over the modular-spinor Grassmannian boundary;
* native filtered topological direct and inverse colimits in `TopCat`.

What it does not own is an analytic theorem identifying the modular-spinor
sheaf spectrum with any specific filtered colimit stage or boundary resolution.
Accordingly, this file only packages the two owner surfaces together and
re-exports the native categorical laws already proved in each.
-/

/-- A joint owner for the modular-spinor sheaf/spectrum bridge and a native
filtered topological direct colimit. -/
structure ModularSpinorFilteredColimitBridge
  {E Sections BoundarySections Gr Open : Type*}
  [AddCommGroup Sections] [Module ℝ Sections]
  [AddCommGroup BoundarySections] [Module ℝ BoundarySections]
  [TopologicalSpace Gr] [Category Open]
  {J : Type u} [Category.{u, u} J]
  (F : J ⥤ TopCat.{u}) where
  spectrumBridge : ModularSpinorGrassmannianSpectrumBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F
  /-- A filtered topological direct colimit stage diagram. -/
  stageDiagram : J ⥤ TopCat.{u}

/-- The sheaf cover condition remains available inside the filtered colimit bridge. -/
theorem modularSpinor_filteredColimit_monogenicSheaf_isSheafFor
  {E Sections BoundarySections Gr Open : Type*}
  [AddCommGroup Sections] [Module ℝ Sections]
  [AddCommGroup BoundarySections] [Module ℝ BoundarySections]
  [TopologicalSpace Gr] [Category Open]
  {J : Type u} [Category.{u, u} J]
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorFilteredColimitBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F) :
    Presieve.IsSheafFor
      B.spectrumBridge.sheafData.sections
      B.spectrumBridge.sheafData.cover :=
  monogenicSheaf_isSheafFor B.spectrumBridge.sheafData

/-- The monogenic section membership theorem remains available inside the
filtered colimit bridge. -/
theorem modularSpinor_filteredColimit_monogenicSection_mem
  {E Sections BoundarySections Gr Open : Type*}
  [AddCommGroup Sections] [Module ℝ Sections]
  [AddCommGroup BoundarySections] [Module ℝ BoundarySections]
  [TopologicalSpace Gr] [Category Open]
  {J : Type u} [Category.{u, u} J]
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorFilteredColimitBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F)
  (U : Open) (s : B.spectrumBridge.sheafData.monogenicSections U) :
    (s : B.spectrumBridge.sheafData.sections.obj (Opposite.op U))
      ∈ B.spectrumBridge.sheafData.monogenicSections U :=
  monogenicSection_mem B.spectrumBridge.sheafData U s

/-- The boundary DN kernel theorem remains available inside the
filtered colimit bridge. -/
theorem modularSpinor_filteredColimit_boundary_kernel_eq_traceMonogenic
  {E Sections BoundarySections Gr Open : Type*}
  [AddCommGroup Sections] [Module ℝ Sections]
  [AddCommGroup BoundarySections] [Module ℝ BoundarySections]
  [TopologicalSpace Gr] [Category Open]
  {J : Type u} [Category.{u, u} J]
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorFilteredColimitBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F) :
    LinearMap.ker
      B.spectrumBridge.boundaryBridge.boundaryData.dirichletToNeumann =
      traceMonogenic B.spectrumBridge.boundaryBridge.boundaryData :=
  boundary_kernel_eq_traceMonogenic B.spectrumBridge.boundaryBridge

/-- The categorical spectrum descent map from the sheaf/spectrum bridge
remains available. -/
noncomputable def modularSpinor_filteredColimit_gelfandSpectrumDescend
  {E Sections BoundarySections Gr Open : Type*}
  [AddCommGroup Sections] [Module ℝ Sections]
  [AddCommGroup BoundarySections] [Module ℝ BoundarySections]
  [TopologicalSpace Gr] [Category Open]
  {J : Type u} [Category.{u, u} J]
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorFilteredColimitBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F) :
    GelfandSpectrum F ⟶ GelfandSpectrum F :=
  modularSpinor_gelfandSpectrumDescend F B.spectrumBridge

/-- The categorical spectrum identification from the sheaf/spectrum bridge
remains available. -/
noncomputable def modularSpinor_filteredColimit_gelfandSpectrumIsoTarget
  {E Sections BoundarySections Gr Open : Type*}
  [AddCommGroup Sections] [Module ℝ Sections]
  [AddCommGroup BoundarySections] [Module ℝ BoundarySections]
  [TopologicalSpace Gr] [Category Open]
  {J : Type u} [Category.{u, u} J]
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorFilteredColimitBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F) :
    GelfandSpectrum F ≅ GelfandSpectrum F :=
  modularSpinor_gelfandSpectrumIsoTarget F B.spectrumBridge

@[reassoc (attr := simp)]
theorem modularSpinor_filteredColimit_gelfandSpectrum_stage
  {E Sections BoundarySections Gr Open : Type*}
  [AddCommGroup Sections] [Module ℝ Sections]
  [AddCommGroup BoundarySections] [Module ℝ BoundarySections]
  [TopologicalSpace Gr] [Category Open]
  {J : Type u} [Category.{u, u} J]
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorFilteredColimitBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F)
  (j : J) :
    colimit.ι F j ≫
      modularSpinor_filteredColimit_gelfandSpectrumDescend F B =
      colimit.ι F j :=
  modularSpinor_gelfandSpectrum_stage F B.spectrumBridge j

/-- The filtered topological direct colimit stage maps are available natively. -/
noncomputable def modularSpinor_filteredColimit_stageInjection
  {E Sections BoundarySections Gr Open : Type*}
  [AddCommGroup Sections] [Module ℝ Sections]
  [AddCommGroup BoundarySections] [Module ℝ BoundarySections]
  [TopologicalSpace Gr] [Category Open]
  {J : Type u} [Category.{u, u} J]
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorFilteredColimitBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F)
  (j : J) : B.stageDiagram.obj j ⟶ colimit B.stageDiagram :=
  colimit.ι B.stageDiagram j

/-- Naturality of the filtered colimit stage maps. -/
theorem modularSpinor_filteredColimit_stageInjection_naturality
  {E Sections BoundarySections Gr Open : Type*}
  [AddCommGroup Sections] [Module ℝ Sections]
  [AddCommGroup BoundarySections] [Module ℝ BoundarySections]
  [TopologicalSpace Gr] [Category Open]
  {J : Type u} [Category.{u, u} J]
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorFilteredColimitBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F)
  {j j' : J} (f : j ⟶ j') :
    B.stageDiagram.map f ≫
      modularSpinor_filteredColimit_stageInjection F B j' =
      modularSpinor_filteredColimit_stageInjection F B j :=
  topologicalDirectInjection_naturality B.stageDiagram f

/-- Modular-spinor transport still preserves the canonical three-form
inside the full filtered colimit bridge. -/
theorem modularSpinor_filteredColimit_transport_preserves_threeForm
  {E Sections BoundarySections Gr Open : Type*}
  [AddCommGroup Sections] [Module ℝ Sections]
  [AddCommGroup BoundarySections] [Module ℝ BoundarySections]
  [TopologicalSpace Gr] [Category Open]
  {J : Type u} [Category.{u, u} J]
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorFilteredColimitBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F)
  (path : List E) (x y z : ModularSpinorCarrier) :
    canonicalSplitG2ThreeFormValue
        (modularSpinorTransport
          B.spectrumBridge.boundaryBridge.connection path x)
        (modularSpinorTransport
          B.spectrumBridge.boundaryBridge.connection path y)
        (modularSpinorTransport
          B.spectrumBridge.boundaryBridge.connection path z) =
      canonicalSplitG2ThreeFormValue x y z := by
  exact bridge_transport_preserves_threeForm
      B.spectrumBridge.boundaryBridge path x y z

end

end InfoGeometry.Canonical
