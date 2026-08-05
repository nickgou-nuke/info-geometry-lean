import InfoGeometry.Canonical.ModularSpinorCuntzStageColimitBridge
import InfoGeometry.Canonical.CuntzStageModularFlowTopologicalIso

namespace InfoGeometry.Canonical

open CategoryTheory
open CategoryTheory.Limits
open FilteredColimit.Native.Topological
open InfoGeometry.Canonical.CuntzStarInductiveSystem
open InfoGeometry.Canonical.CuntzStageModularFlow

noncomputable section

universe u

/-!
# Modular-spinor / Cuntz-stage modular flow topological isomorphism bridge

This file adds the next honest node after
`ModularSpinorCuntzStageColimitBridge`. The current repository already owns:

* a Cuntz-stage colimit bridge over the modular-spinor sheaf/spectrum;
* a genuine Cuntz-stage modular flow topological isomorphism (`modularFlowTopologicalColimitIso`)
  with group laws (`modularFlowTopologicalColimitIso_add`, `modularFlowTopologicalColimitIso_zero`).

What it does not own is an analytic theorem identifying the modular-spinor
sheaf spectrum with any specific Cuntz modular flow stage or KMS invariance.
Accordingly, this file only packages the two owner surfaces together and
re-exports the native categorical laws already proved in each.
-/

variable {E Sections BoundarySections Gr Open : Type*}
variable [AddCommGroup Sections] [Module ℝ Sections]
variable [AddCommGroup BoundarySections] [Module ℝ BoundarySections]
variable [TopologicalSpace Gr] [Category Open]
variable {J : Type u} [Category.{u, u} J]
variable {F : J ⥤ TopCat.{u}}

/-- A joint owner for the modular-spinor Cuntz-stage colimit bridge and the
Cuntz-stage modular flow topological isomorphism. -/
abbrev ModularSpinorCuntzStageTopologicalIsoBridge
  {E Sections BoundarySections Gr Open : Type*}
  [AddCommGroup Sections] [Module ℝ Sections]
  [AddCommGroup BoundarySections] [Module ℝ BoundarySections]
  [TopologicalSpace Gr] [Category Open]
  {J : Type u} [Category.{u, u} J]
  (F : J ⥤ TopCat.{u}) :=
  ModularSpinorCuntzStageColimitBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F

namespace ModularSpinorCuntzStageTopologicalIsoBridge

/-- Compatibility projection for the former one-field wrapper. -/
abbrev cuntzStageColimitBridge
  {E Sections BoundarySections Gr Open : Type*}
  [AddCommGroup Sections] [Module ℝ Sections]
  [AddCommGroup BoundarySections] [Module ℝ BoundarySections]
  [TopologicalSpace Gr] [Category Open]
  {J : Type u} [Category.{u, u} J]
  {F : J ⥤ TopCat.{u}}
  (B : ModularSpinorCuntzStageTopologicalIsoBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F) := B

end ModularSpinorCuntzStageTopologicalIsoBridge

/-- The sheaf cover condition remains available inside the topological isomorphism bridge. -/
theorem modularSpinor_CuntzStageTopologicalIso_monogenicSheaf_isSheafFor
  {E Sections BoundarySections Gr Open : Type*}
  [AddCommGroup Sections] [Module ℝ Sections]
  [AddCommGroup BoundarySections] [Module ℝ BoundarySections]
  [TopologicalSpace Gr] [Category Open]
  {J : Type u} [Category.{u, u} J]
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorCuntzStageTopologicalIsoBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F) :
    Presieve.IsSheafFor
      B.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.sheafData.sections
      B.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.sheafData.cover :=
  modularSpinor_CuntzStageColimit_monogenicSheaf_isSheafFor F B.cuntzStageColimitBridge

/-- The monogenic section membership theorem remains available inside the
topological isomorphism bridge. -/
theorem modularSpinor_CuntzStageTopologicalIso_monogenicSection_mem
  {E Sections BoundarySections Gr Open : Type*}
  [AddCommGroup Sections] [Module ℝ Sections]
  [AddCommGroup BoundarySections] [Module ℝ BoundarySections]
  [TopologicalSpace Gr] [Category Open]
  {J : Type u} [Category.{u, u} J]
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorCuntzStageTopologicalIsoBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F)
  (U : Open) (s : B.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.sheafData.monogenicSections U) :
    (s : B.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.sheafData.sections.obj (Opposite.op U))
      ∈ B.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.sheafData.monogenicSections U :=
  modularSpinor_CuntzStageColimit_monogenicSection_mem F B.cuntzStageColimitBridge U s

/-- The boundary DN kernel theorem remains available inside the
topological isomorphism bridge. -/
theorem modularSpinor_CuntzStageTopologicalIso_boundary_kernel_eq_traceMonogenic
  {E Sections BoundarySections Gr Open : Type*}
  [AddCommGroup Sections] [Module ℝ Sections]
  [AddCommGroup BoundarySections] [Module ℝ BoundarySections]
  [TopologicalSpace Gr] [Category Open]
  {J : Type u} [Category.{u, u} J]
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorCuntzStageTopologicalIsoBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F) :
    LinearMap.ker
      B.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.boundaryBridge.boundaryData.dirichletToNeumann =
      traceMonogenic B.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.boundaryBridge.boundaryData :=
  modularSpinor_CuntzStageColimit_boundary_kernel_eq_traceMonogenic F B.cuntzStageColimitBridge

/-- The categorical spectrum descent map from the sheaf/spectrum bridge
remains available inside the topological isomorphism bridge. -/
noncomputable def modularSpinor_CuntzStageTopologicalIso_gelfandSpectrumDescend
  {E Sections BoundarySections Gr Open : Type*}
  [AddCommGroup Sections] [Module ℝ Sections]
  [AddCommGroup BoundarySections] [Module ℝ BoundarySections]
  [TopologicalSpace Gr] [Category Open]
  {J : Type u} [Category.{u, u} J]
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorCuntzStageTopologicalIsoBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F) :
    GelfandSpectrum F ⟶ GelfandSpectrum F :=
  modularSpinor_CuntzStageColimit_gelfandSpectrumDescend F B.cuntzStageColimitBridge

/-- The categorical spectrum identification from the sheaf/spectrum bridge
remains available inside the topological isomorphism bridge. -/
noncomputable def modularSpinor_CuntzStageTopologicalIso_gelfandSpectrumIsoTarget
  {E Sections BoundarySections Gr Open : Type*}
  [AddCommGroup Sections] [Module ℝ Sections]
  [AddCommGroup BoundarySections] [Module ℝ BoundarySections]
  [TopologicalSpace Gr] [Category Open]
  {J : Type u} [Category.{u, u} J]
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorCuntzStageTopologicalIsoBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F) :
    GelfandSpectrum F ≅ GelfandSpectrum F :=
  modularSpinor_CuntzStageColimit_gelfandSpectrumIsoTarget F B.cuntzStageColimitBridge

@[reassoc (attr := simp)]
theorem modularSpinor_CuntzStageTopologicalIso_gelfandSpectrum_stage
  {E Sections BoundarySections Gr Open : Type*}
  [AddCommGroup Sections] [Module ℝ Sections]
  [AddCommGroup BoundarySections] [Module ℝ BoundarySections]
  [TopologicalSpace Gr] [Category Open]
  {J : Type u} [Category.{u, u} J]
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorCuntzStageTopologicalIsoBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F)
  (j : J) :
    colimit.ι F j ≫
      modularSpinor_CuntzStageTopologicalIso_gelfandSpectrumDescend F B =
      colimit.ι F j :=
  by
  dsimp only [modularSpinor_CuntzStageTopologicalIso_gelfandSpectrumDescend] at *
  exact modularSpinor_CuntzStageColimit_gelfandSpectrum_stage F B.cuntzStageColimitBridge j

/-- The filtered topological direct colimit stage maps remain available
inside the topological isomorphism bridge. -/
noncomputable def modularSpinor_CuntzStageTopologicalIso_stageInjection
  {E Sections BoundarySections Gr Open : Type*}
  [AddCommGroup Sections] [Module ℝ Sections]
  [AddCommGroup BoundarySections] [Module ℝ BoundarySections]
  [TopologicalSpace Gr] [Category Open]
  {J : Type u} [Category.{u, u} J]
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorCuntzStageTopologicalIsoBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F)
  (j : J) : B.cuntzStageColimitBridge.filteredColimitBridge.stageDiagram.obj j ⟶ colimit B.cuntzStageColimitBridge.filteredColimitBridge.stageDiagram :=
  modularSpinor_CuntzStageColimit_stageInjection F B.cuntzStageColimitBridge j

/-- Naturality of the filtered colimit stage maps remains available
inside the topological isomorphism bridge. -/
theorem modularSpinor_CuntzStageTopologicalIso_stageInjection_naturality
  {E Sections BoundarySections Gr Open : Type*}
  [AddCommGroup Sections] [Module ℝ Sections]
  [AddCommGroup BoundarySections] [Module ℝ BoundarySections]
  [TopologicalSpace Gr] [Category Open]
  {J : Type u} [Category.{u, u} J]
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorCuntzStageTopologicalIsoBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F)
  {j j' : J} (f : j ⟶ j') :
    B.cuntzStageColimitBridge.filteredColimitBridge.stageDiagram.map f ≫
      modularSpinor_CuntzStageTopologicalIso_stageInjection F B j' =
      modularSpinor_CuntzStageTopologicalIso_stageInjection F B j :=
  by
  dsimp only [modularSpinor_CuntzStageTopologicalIso_stageInjection] at *
  exact modularSpinor_CuntzStageColimit_stageInjection_naturality F B.cuntzStageColimitBridge f

/-- Modular-spinor transport still preserves the canonical three-form
inside the full topological isomorphism bridge. -/
theorem modularSpinor_CuntzStageTopologicalIso_transport_preserves_threeForm
  {E Sections BoundarySections Gr Open : Type*}
  [AddCommGroup Sections] [Module ℝ Sections]
  [AddCommGroup BoundarySections] [Module ℝ BoundarySections]
  [TopologicalSpace Gr] [Category Open]
  {J : Type u} [Category.{u, u} J]
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorCuntzStageTopologicalIsoBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F)
  (path : List E) (x y z : ModularSpinorCarrier) :
    canonicalSplitG2ThreeFormValue
        ((modularSpinorTransport
          B.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.boundaryBridge.connection path) x)
        ((modularSpinorTransport
          B.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.boundaryBridge.connection path) y)
        ((modularSpinorTransport
          B.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.boundaryBridge.connection path) z) =
      canonicalSplitG2ThreeFormValue x y z := by
  have h := modularSpinor_CuntzStageColimit_transport_preserves_threeForm F B.cuntzStageColimitBridge path x y z
  simp_all [modularSpinorTransport]
  <;>
  exact h

end

end InfoGeometry.Canonical
