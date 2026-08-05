import InfoGeometry.Canonical.ModularSpinorCl11MarkovJonesTopologicalColimitBridge
import InfoGeometry.Canonical.Cl11MarkovJonesTopologicalCyclicTransport

namespace InfoGeometry.Canonical

open CategoryTheory
open CategoryTheory.Limits
open FilteredColimit.Native.Topological
open InfoGeometry.Canonical.Cl11MarkovJonesTopologicalColimit
open InfoGeometry.Canonical.Cl11MarkovJonesTopologicalCyclicTransport
open InfoGeometry.Clifford.Cl11TensorTower

noncomputable section

universe u

/-!
# Modular-spinor / Cl(1,1) Markov-Jones cyclic transport bridge

This file adds the next honest node after
`ModularSpinorCl11MarkovJonesTopologicalColimitBridge`. The repository already owns:

* a modular-spinor / Cl(1,1) Markov-Jones topological colimit bridge;
* a genuine finite `Cl(1,1)` cyclic transport/readout lane on the native
  topological colimit.

What it does not own is a theorem identifying the modular-spinor sheaf/spectrum
lane with the `Cl(1,1)` cyclic transport family or proving exchange/KMS
compatibility with that transport. Accordingly, this file only packages the
existing owner surfaces together and re-exports the native facts already proved
in each.
-/

variable {E Sections BoundarySections Gr Open : Type*}
variable [AddCommGroup Sections] [Module ℝ Sections]
variable [AddCommGroup BoundarySections] [Module ℝ BoundarySections]
variable [TopologicalSpace Gr] [Category Open]
variable {J : Type u} [Category.{u, u} J]

/-- A joint owner for the modular-spinor/Cl(1,1) Markov-Jones colimit bridge
and the finite cyclic transport lane. -/
abbrev ModularSpinorCl11MarkovJonesTopologicalCyclicBridge
  {E Sections BoundarySections Gr Open : Type*}
  [AddCommGroup Sections] [Module ℝ Sections]
  [AddCommGroup BoundarySections] [Module ℝ BoundarySections]
  [TopologicalSpace Gr] [Category Open]
  {J : Type u} [Category.{u, u} J]
  (F : J ⥤ TopCat.{u}) :=
  ModularSpinorCl11MarkovJonesTopologicalColimitBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F

namespace ModularSpinorCl11MarkovJonesTopologicalCyclicBridge

/-- Compatibility projection for the former one-field wrapper. -/
abbrev colimitBridge
  {E Sections BoundarySections Gr Open : Type*}
  [AddCommGroup Sections] [Module ℝ Sections]
  [AddCommGroup BoundarySections] [Module ℝ BoundarySections]
  [TopologicalSpace Gr] [Category Open]
  {J : Type u} [Category.{u, u} J]
  {F : J ⥤ TopCat.{u}}
  (B : ModularSpinorCl11MarkovJonesTopologicalCyclicBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F) := B

end ModularSpinorCl11MarkovJonesTopologicalCyclicBridge

/-- The sheaf cover condition remains available inside the cyclic-transport
bridge. -/
theorem modularSpinor_Cl11MarkovJonesTopologicalCyclic_monogenicSheaf_isSheafFor
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorCl11MarkovJonesTopologicalCyclicBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F) :
    Presieve.IsSheafFor
      B.colimitBridge.complexificationBridge.exchangeBridge.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.sheafData.sections
      B.colimitBridge.complexificationBridge.exchangeBridge.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.sheafData.cover :=
  modularSpinor_Cl11MarkovJonesTopologicalColimit_monogenicSheaf_isSheafFor F B.colimitBridge

/-- Monogenic section membership remains available inside the cyclic-transport
bridge. -/
theorem modularSpinor_Cl11MarkovJonesTopologicalCyclic_monogenicSection_mem
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorCl11MarkovJonesTopologicalCyclicBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F)
  (U : Open)
  (s : B.colimitBridge.complexificationBridge.exchangeBridge.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.sheafData.monogenicSections U) :
    (s : B.colimitBridge.complexificationBridge.exchangeBridge.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.sheafData.sections.obj (Opposite.op U))
      ∈ B.colimitBridge.complexificationBridge.exchangeBridge.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.sheafData.monogenicSections U :=
  modularSpinor_Cl11MarkovJonesTopologicalColimit_monogenicSection_mem F B.colimitBridge U s

/-- The DN-kernel identity remains available inside the cyclic-transport bridge. -/
theorem modularSpinor_Cl11MarkovJonesTopologicalCyclic_boundary_kernel_eq_traceMonogenic
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorCl11MarkovJonesTopologicalCyclicBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F) :
    LinearMap.ker
      B.colimitBridge.complexificationBridge.exchangeBridge.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.boundaryBridge.boundaryData.dirichletToNeumann =
      traceMonogenic B.colimitBridge.complexificationBridge.exchangeBridge.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.boundaryBridge.boundaryData :=
  modularSpinor_Cl11MarkovJonesTopologicalColimit_boundary_kernel_eq_traceMonogenic F B.colimitBridge

/-- Gelfand-spectrum descent remains available inside the cyclic-transport bridge. -/
noncomputable def modularSpinor_Cl11MarkovJonesTopologicalCyclic_gelfandSpectrumDescend
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorCl11MarkovJonesTopologicalCyclicBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F) :
    GelfandSpectrum F ⟶ GelfandSpectrum F :=
  modularSpinor_Cl11MarkovJonesTopologicalColimit_gelfandSpectrumDescend F B.colimitBridge

/-- Gelfand-spectrum target identification remains available inside the
cyclic-transport bridge. -/
noncomputable def modularSpinor_Cl11MarkovJonesTopologicalCyclic_gelfandSpectrumIsoTarget
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorCl11MarkovJonesTopologicalCyclicBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F) :
    GelfandSpectrum F ≅ GelfandSpectrum F :=
  modularSpinor_Cl11MarkovJonesTopologicalColimit_gelfandSpectrumIsoTarget F B.colimitBridge

@[reassoc (attr := simp)]
theorem modularSpinor_Cl11MarkovJonesTopologicalCyclic_gelfandSpectrum_stage
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorCl11MarkovJonesTopologicalCyclicBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F)
  (j : J) :
    colimit.ι F j ≫
      modularSpinor_Cl11MarkovJonesTopologicalCyclic_gelfandSpectrumDescend F B =
      colimit.ι F j := by
  dsimp only [modularSpinor_Cl11MarkovJonesTopologicalCyclic_gelfandSpectrumDescend] at *
  exact modularSpinor_Cl11MarkovJonesTopologicalColimit_gelfandSpectrum_stage F B.colimitBridge j

/-- Filtered-colimit stage injections remain available inside the cyclic-transport
bridge. -/
noncomputable def modularSpinor_Cl11MarkovJonesTopologicalCyclic_stageInjection
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorCl11MarkovJonesTopologicalCyclicBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F)
  (j : J) :
    B.colimitBridge.complexificationBridge.exchangeBridge.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.stageDiagram.obj j ⟶
      colimit B.colimitBridge.complexificationBridge.exchangeBridge.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.stageDiagram :=
  modularSpinor_Cl11MarkovJonesTopologicalColimit_stageInjection F B.colimitBridge j

/-- Naturality of the filtered-colimit stage injections remains available inside
the cyclic-transport bridge. -/
theorem modularSpinor_Cl11MarkovJonesTopologicalCyclic_stageInjection_naturality
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorCl11MarkovJonesTopologicalCyclicBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F)
  {j j' : J} (f : j ⟶ j') :
    B.colimitBridge.complexificationBridge.exchangeBridge.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.stageDiagram.map f ≫
      modularSpinor_Cl11MarkovJonesTopologicalCyclic_stageInjection F B j' =
      modularSpinor_Cl11MarkovJonesTopologicalCyclic_stageInjection F B j := by
  dsimp only [modularSpinor_Cl11MarkovJonesTopologicalCyclic_stageInjection] at *
  exact modularSpinor_Cl11MarkovJonesTopologicalColimit_stageInjection_naturality F B.colimitBridge f

/-- Modular-spinor transport still preserves the canonical three-form inside the
full cyclic-transport bridge. -/
theorem modularSpinor_Cl11MarkovJonesTopologicalCyclic_transport_preserves_threeForm
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorCl11MarkovJonesTopologicalCyclicBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F)
  (path : List E) (x y z : ModularSpinorCarrier) :
    canonicalSplitG2ThreeFormValue
        ((modularSpinorTransport
          B.colimitBridge.complexificationBridge.exchangeBridge.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.boundaryBridge.connection path) x)
        ((modularSpinorTransport
          B.colimitBridge.complexificationBridge.exchangeBridge.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.boundaryBridge.connection path) y)
        ((modularSpinorTransport
          B.colimitBridge.complexificationBridge.exchangeBridge.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.boundaryBridge.connection path) z) =
      canonicalSplitG2ThreeFormValue x y z := by
  have h := modularSpinor_Cl11MarkovJonesTopologicalColimit_transport_preserves_threeForm F B.colimitBridge path x y z
  simp_all [modularSpinorTransport]
  <;> exact h

/-- Conjugation invariance of the finite topological Markov-trace readout remains
available inside the joint bridge. -/
theorem cl11MarkovJones_traceColimit_conjugation_invariant
  (u uInv : StageFamily)
  (hu : ∀ {m n : ℕ} (h : m ≤ n), stageEmbedMap h (u m) = u n)
  (huInv : ∀ {m n : ℕ} (h : m ≤ n), stageEmbedMap h (uInv m) = uInv n)
  (hunit : ∀ n, uInv n * u n = 1) :
    colim.map (conjugationNatTrans u uInv hu huInv) ≫
        traceTopologicalColimitMap =
      traceTopologicalColimitMap :=
  traceColimit_conjugation_invariant u uInv hu huInv hunit

/-- Left/right compatible family cyclicity remains available inside the joint
bridge. -/
theorem cl11MarkovJones_traceColimit_leftRight_compatible_family
  (a : StageFamily)
  (ha : ∀ {m n : ℕ} (h : m ≤ n), stageEmbedMap h (a m) = a n)
  (b : StageFamily)
  (hb : ∀ {m n : ℕ} (h : m ≤ n), stageEmbedMap h (b m) = b n) :
    colim.map (leftMultiplicationNatTrans a ha) ≫
        colim.map (rightMultiplicationNatTrans b hb) ≫
        traceTopologicalColimitMap =
      colim.map (rightMultiplicationNatTrans b hb) ≫
        colim.map (leftMultiplicationNatTrans a ha) ≫
        traceTopologicalColimitMap :=
  traceColimit_leftRight_compatible_family a ha b hb

/-- The inherited Markov-Jones topological trace readout remains uniquely
determined by the stagewise normalized traces inside the cyclic bridge. -/
theorem cl11MarkovJones_cyclicBridge_topologicalTraceReadout_unique
  (f : topologicalColimitObject ⟶ TopCat.of ℝ)
  (h : ∀ (n : ℕ) (A : MatStage n),
    f (topologicalInclusion n A) = normalizedTrace n A) :
    f = cl11MarkovJones_topologicalTraceReadout := by
  exact InfoGeometry.Canonical.cl11MarkovJones_topologicalTraceReadout_unique f h

end

end InfoGeometry.Canonical
