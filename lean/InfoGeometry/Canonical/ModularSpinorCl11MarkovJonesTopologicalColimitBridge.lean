import InfoGeometry.Canonical.ModularSpinorCl11CuntzStageComplexificationBridge
import InfoGeometry.Canonical.Cl11MarkovJonesTopologicalColimit

namespace InfoGeometry.Canonical

open CategoryTheory
open CategoryTheory.Limits
open FilteredColimit.Native.Topological
open InfoGeometry.Canonical.Cl11MarkovJonesTopologicalColimit
open InfoGeometry.Clifford.Cl11TensorTower

noncomputable section

universe u

/-!
# Modular-spinor / Cl(1,1) Markov-Jones topological colimit bridge

This file adds the next honest node after
`ModularSpinorCl11CuntzStageComplexificationBridge`. The repository already owns:

* a modular-spinor / Cl(1,1)-to-Cuntz stage complexification bridge;
* a genuine finite `Cl(1,1)` Markov-trace topological colimit/readout lane.

What it does not own is a theorem identifying the modular-spinor sheaf/spectrum
lane with the `Cl(1,1)` Markov-Jones tower or proving exchange/KMS
compatibility with that trace colimit. Accordingly, this file only packages the
existing owner surfaces together and re-exports the native facts already proved
in each.
-/

variable {E Sections BoundarySections Gr Open : Type*}
variable [AddCommGroup Sections] [Module ℝ Sections]
variable [AddCommGroup BoundarySections] [Module ℝ BoundarySections]
variable [TopologicalSpace Gr] [Category Open]
variable {J : Type u} [Category.{u, u} J]

/-- A joint owner for the modular-spinor/Cl(1,1)-Cuntz bridge and the finite
`Cl(1,1)` Markov-Jones topological colimit lane. -/
abbrev ModularSpinorCl11MarkovJonesTopologicalColimitBridge
  {E Sections BoundarySections Gr Open : Type*}
  [AddCommGroup Sections] [Module ℝ Sections]
  [AddCommGroup BoundarySections] [Module ℝ BoundarySections]
  [TopologicalSpace Gr] [Category Open]
  {J : Type u} [Category.{u, u} J]
  (F : J ⥤ TopCat.{u}) :=
  ModularSpinorCl11CuntzStageComplexificationBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F

namespace ModularSpinorCl11MarkovJonesTopologicalColimitBridge

/-- Compatibility projection for the former one-field wrapper. -/
abbrev complexificationBridge
  {E Sections BoundarySections Gr Open : Type*}
  [AddCommGroup Sections] [Module ℝ Sections]
  [AddCommGroup BoundarySections] [Module ℝ BoundarySections]
  [TopologicalSpace Gr] [Category Open]
  {J : Type u} [Category.{u, u} J]
  {F : J ⥤ TopCat.{u}}
  (B : ModularSpinorCl11MarkovJonesTopologicalColimitBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F) := B

end ModularSpinorCl11MarkovJonesTopologicalColimitBridge

/-- The sheaf cover condition remains available inside the Markov-Jones
colimit bridge. -/
theorem modularSpinor_Cl11MarkovJonesTopologicalColimit_monogenicSheaf_isSheafFor
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorCl11MarkovJonesTopologicalColimitBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F) :
    Presieve.IsSheafFor
      B.complexificationBridge.exchangeBridge.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.sheafData.sections
      B.complexificationBridge.exchangeBridge.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.sheafData.cover :=
  modularSpinor_Cl11CuntzStageComplexification_monogenicSheaf_isSheafFor F B.complexificationBridge

/-- Monogenic section membership remains available inside the Markov-Jones
colimit bridge. -/
theorem modularSpinor_Cl11MarkovJonesTopologicalColimit_monogenicSection_mem
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorCl11MarkovJonesTopologicalColimitBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F)
  (U : Open)
  (s : B.complexificationBridge.exchangeBridge.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.sheafData.monogenicSections U) :
    (s : B.complexificationBridge.exchangeBridge.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.sheafData.sections.obj (Opposite.op U))
      ∈ B.complexificationBridge.exchangeBridge.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.sheafData.monogenicSections U :=
  modularSpinor_Cl11CuntzStageComplexification_monogenicSection_mem F B.complexificationBridge U s

/-- The DN-kernel identity remains available inside the Markov-Jones colimit
bridge. -/
theorem modularSpinor_Cl11MarkovJonesTopologicalColimit_boundary_kernel_eq_traceMonogenic
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorCl11MarkovJonesTopologicalColimitBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F) :
    LinearMap.ker
      B.complexificationBridge.exchangeBridge.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.boundaryBridge.boundaryData.dirichletToNeumann =
      traceMonogenic B.complexificationBridge.exchangeBridge.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.boundaryBridge.boundaryData :=
  modularSpinor_Cl11CuntzStageComplexification_boundary_kernel_eq_traceMonogenic F B.complexificationBridge

/-- Gelfand-spectrum descent remains available inside the Markov-Jones colimit
bridge. -/
noncomputable def modularSpinor_Cl11MarkovJonesTopologicalColimit_gelfandSpectrumDescend
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorCl11MarkovJonesTopologicalColimitBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F) :
    GelfandSpectrum F ⟶ GelfandSpectrum F :=
  modularSpinor_Cl11CuntzStageComplexification_gelfandSpectrumDescend F B.complexificationBridge

/-- Gelfand-spectrum target identification remains available inside the
Markov-Jones colimit bridge. -/
noncomputable def modularSpinor_Cl11MarkovJonesTopologicalColimit_gelfandSpectrumIsoTarget
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorCl11MarkovJonesTopologicalColimitBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F) :
    GelfandSpectrum F ≅ GelfandSpectrum F :=
  modularSpinor_Cl11CuntzStageComplexification_gelfandSpectrumIsoTarget F B.complexificationBridge

@[reassoc (attr := simp)]
theorem modularSpinor_Cl11MarkovJonesTopologicalColimit_gelfandSpectrum_stage
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorCl11MarkovJonesTopologicalColimitBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F)
  (j : J) :
    colimit.ι F j ≫
      modularSpinor_Cl11MarkovJonesTopologicalColimit_gelfandSpectrumDescend F B =
      colimit.ι F j := by
  dsimp only [modularSpinor_Cl11MarkovJonesTopologicalColimit_gelfandSpectrumDescend] at *
  exact modularSpinor_Cl11CuntzStageComplexification_gelfandSpectrum_stage F B.complexificationBridge j

/-- Filtered-colimit stage injections remain available inside the Markov-Jones
colimit bridge. -/
noncomputable def modularSpinor_Cl11MarkovJonesTopologicalColimit_stageInjection
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorCl11MarkovJonesTopologicalColimitBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F)
  (j : J) :
    B.complexificationBridge.exchangeBridge.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.stageDiagram.obj j ⟶
      colimit B.complexificationBridge.exchangeBridge.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.stageDiagram :=
  modularSpinor_Cl11CuntzStageComplexification_stageInjection F B.complexificationBridge j

/-- Naturality of the filtered-colimit stage injections remains available inside
the Markov-Jones colimit bridge. -/
theorem modularSpinor_Cl11MarkovJonesTopologicalColimit_stageInjection_naturality
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorCl11MarkovJonesTopologicalColimitBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F)
  {j j' : J} (f : j ⟶ j') :
    B.complexificationBridge.exchangeBridge.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.stageDiagram.map f ≫
      modularSpinor_Cl11MarkovJonesTopologicalColimit_stageInjection F B j' =
      modularSpinor_Cl11MarkovJonesTopologicalColimit_stageInjection F B j := by
  dsimp only [modularSpinor_Cl11MarkovJonesTopologicalColimit_stageInjection] at *
  exact modularSpinor_Cl11CuntzStageComplexification_stageInjection_naturality F B.complexificationBridge f

/-- Modular-spinor transport still preserves the canonical three-form inside the
full Markov-Jones colimit bridge. -/
theorem modularSpinor_Cl11MarkovJonesTopologicalColimit_transport_preserves_threeForm
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorCl11MarkovJonesTopologicalColimitBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F)
  (path : List E) (x y z : ModularSpinorCarrier) :
    canonicalSplitG2ThreeFormValue
        ((modularSpinorTransport
          B.complexificationBridge.exchangeBridge.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.boundaryBridge.connection path) x)
        ((modularSpinorTransport
          B.complexificationBridge.exchangeBridge.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.boundaryBridge.connection path) y)
        ((modularSpinorTransport
          B.complexificationBridge.exchangeBridge.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.boundaryBridge.connection path) z) =
      canonicalSplitG2ThreeFormValue x y z := by
  have h := modularSpinor_Cl11CuntzStageComplexification_transport_preserves_threeForm F B.complexificationBridge path x y z
  simp_all [modularSpinorTransport]
  <;> exact h

/-- Iterated stage embeddings along `m ≤ n` remain available inside the joint
bridge. -/
theorem cl11MarkovJones_stageEmbedMap_comp
  {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    (stageEmbedMap hnk).comp (stageEmbedMap hmn) =
      stageEmbedMap (hmn.trans hnk) :=
  stageEmbedMap_comp hmn hnk

/-- The finite normalized trace descends through iterated stage embeddings. -/
theorem cl11MarkovJones_normalizedTrace_stageEmbedMap
  {m n : ℕ} (h : m ≤ n) (A : MatStage m) :
    normalizedTrace n (stageEmbedMap h A) = normalizedTrace m A :=
  normalizedTrace_stageEmbedMap h A

/-- The topological finite normalized-trace cocone remains available inside the
joint bridge. -/
noncomputable def cl11MarkovJones_traceTopologicalCocone : Cocone topologicalDiagram :=
  traceTopologicalCocone

/-- The finite topological trace readout on the direct colimit remains available
inside the joint bridge. -/
noncomputable def cl11MarkovJones_topologicalTraceReadout :
    topologicalColimitObject ⟶ TopCat.of ℝ :=
  traceTopologicalColimitMap

@[simp] theorem cl11MarkovJones_topologicalTraceReadout_apply
  (n : ℕ) (A : MatStage n) :
    cl11MarkovJones_topologicalTraceReadout
      (topologicalInclusion n A) = normalizedTrace n A :=
  traceTopologicalColimitMap_inclusion n A

/-- The Markov-Jones topological trace readout is uniquely determined by the
stagewise normalized traces. -/
theorem cl11MarkovJones_topologicalTraceReadout_unique
  (f : topologicalColimitObject ⟶ TopCat.of ℝ)
  (h : ∀ (n : ℕ) (A : MatStage n),
    f (topologicalInclusion n A) = normalizedTrace n A) :
    f = cl11MarkovJones_topologicalTraceReadout := by
  simpa [cl11MarkovJones_topologicalTraceReadout] using
    traceTopologicalColimitMap_unique f h

end

end InfoGeometry.Canonical
