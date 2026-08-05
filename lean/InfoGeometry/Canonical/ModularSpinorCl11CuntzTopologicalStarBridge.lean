import InfoGeometry.Canonical.ModularSpinorCl11MarkovJonesTopologicalCyclicBridge
import InfoGeometry.Canonical.Cl11CuntzTopologicalStarReadout

namespace InfoGeometry.Canonical

open CategoryTheory
open CategoryTheory.Limits
open FilteredColimit.Native.Topological
open InfoGeometry.Canonical.Cl11CuntzTopologicalStarReadout
open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.Canonical.CuntzMatrixTraceTower
open InfoGeometry.Canonical.CuntzMatrixTraceTopologicalColimit
open InfoGeometry.Canonical.Cl11CuntzCoherentIndexTopologicalBridge
open InfoGeometry.Clifford.Cl11TensorTowerLimit

noncomputable section

universe u

/-!
# Modular-spinor / Cl(1,1)-Cuntz topological star bridge

This file adds the next honest node after
`ModularSpinorCl11MarkovJonesTopologicalCyclicBridge`. The repository already owns:

* a modular-spinor / Cl(1,1) Markov-Jones cyclic transport bridge;
* a genuine continuous involution readout on the Cl(1,1)-Cuntz matrix colimit.

What it does not own is a theorem identifying the modular-spinor sheaf/spectrum
lane with the Cuntz-side involution readout or proving exchange/KMS
compatibility with that involution. Accordingly, this file only packages the
existing owner surfaces together and re-exports the native facts already proved
in each.
-/

variable {E Sections BoundarySections Gr Open : Type*}
variable [AddCommGroup Sections] [Module ℝ Sections]
variable [AddCommGroup BoundarySections] [Module ℝ BoundarySections]
variable [TopologicalSpace Gr] [Category Open]
variable {J : Type u} [Category.{u, u} J]

/-- A joint owner for the modular-spinor/Cl(1,1) cyclic bridge and the
Cuntz-side continuous involution readout. -/
abbrev ModularSpinorCl11CuntzTopologicalStarBridge
  {E Sections BoundarySections Gr Open : Type*}
  [AddCommGroup Sections] [Module ℝ Sections]
  [AddCommGroup BoundarySections] [Module ℝ BoundarySections]
  [TopologicalSpace Gr] [Category Open]
  {J : Type u} [Category.{u, u} J]
  (F : J ⥤ TopCat.{u}) :=
  ModularSpinorCl11MarkovJonesTopologicalCyclicBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F

namespace ModularSpinorCl11CuntzTopologicalStarBridge

/-- Compatibility projection for the former one-field wrapper. -/
abbrev cyclicBridge
  {E Sections BoundarySections Gr Open : Type*}
  [AddCommGroup Sections] [Module ℝ Sections]
  [AddCommGroup BoundarySections] [Module ℝ BoundarySections]
  [TopologicalSpace Gr] [Category Open]
  {J : Type u} [Category.{u, u} J]
  {F : J ⥤ TopCat.{u}}
  (B : ModularSpinorCl11CuntzTopologicalStarBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F) := B

end ModularSpinorCl11CuntzTopologicalStarBridge

/-- The sheaf cover condition remains available inside the topological star
bridge. -/
theorem modularSpinor_Cl11CuntzTopologicalStar_monogenicSheaf_isSheafFor
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorCl11CuntzTopologicalStarBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F) :
    Presieve.IsSheafFor
      B.cyclicBridge.colimitBridge.complexificationBridge.exchangeBridge.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.sheafData.sections
      B.cyclicBridge.colimitBridge.complexificationBridge.exchangeBridge.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.sheafData.cover :=
  modularSpinor_Cl11MarkovJonesTopologicalCyclic_monogenicSheaf_isSheafFor F B.cyclicBridge

/-- Monogenic section membership remains available inside the topological star
bridge. -/
theorem modularSpinor_Cl11CuntzTopologicalStar_monogenicSection_mem
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorCl11CuntzTopologicalStarBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F)
  (U : Open)
  (s : B.cyclicBridge.colimitBridge.complexificationBridge.exchangeBridge.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.sheafData.monogenicSections U) :
    (s : B.cyclicBridge.colimitBridge.complexificationBridge.exchangeBridge.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.sheafData.sections.obj (Opposite.op U))
      ∈ B.cyclicBridge.colimitBridge.complexificationBridge.exchangeBridge.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.sheafData.monogenicSections U :=
  modularSpinor_Cl11MarkovJonesTopologicalCyclic_monogenicSection_mem F B.cyclicBridge U s

/-- The DN-kernel identity remains available inside the topological star
bridge. -/
theorem modularSpinor_Cl11CuntzTopologicalStar_boundary_kernel_eq_traceMonogenic
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorCl11CuntzTopologicalStarBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F) :
    LinearMap.ker
      B.cyclicBridge.colimitBridge.complexificationBridge.exchangeBridge.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.boundaryBridge.boundaryData.dirichletToNeumann =
      traceMonogenic B.cyclicBridge.colimitBridge.complexificationBridge.exchangeBridge.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.boundaryBridge.boundaryData :=
  modularSpinor_Cl11MarkovJonesTopologicalCyclic_boundary_kernel_eq_traceMonogenic F B.cyclicBridge

/-- Gelfand-spectrum descent remains available inside the topological star
bridge. -/
noncomputable def modularSpinor_Cl11CuntzTopologicalStar_gelfandSpectrumDescend
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorCl11CuntzTopologicalStarBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F) :
    GelfandSpectrum F ⟶ GelfandSpectrum F :=
  modularSpinor_Cl11MarkovJonesTopologicalCyclic_gelfandSpectrumDescend F B.cyclicBridge

@[reassoc (attr := simp)]
theorem modularSpinor_Cl11CuntzTopologicalStar_gelfandSpectrum_stage
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorCl11CuntzTopologicalStarBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F)
  (j : J) :
    colimit.ι F j ≫
      modularSpinor_Cl11CuntzTopologicalStar_gelfandSpectrumDescend F B =
      colimit.ι F j := by
  dsimp only [modularSpinor_Cl11CuntzTopologicalStar_gelfandSpectrumDescend] at *
  exact modularSpinor_Cl11MarkovJonesTopologicalCyclic_gelfandSpectrum_stage F B.cyclicBridge j

/-- Modular-spinor transport still preserves the canonical three-form inside the
full topological star bridge. -/
theorem modularSpinor_Cl11CuntzTopologicalStar_transport_preserves_threeForm
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorCl11CuntzTopologicalStarBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F)
  (path : List E) (x y z : ModularSpinorCarrier) :
    canonicalSplitG2ThreeFormValue
        ((modularSpinorTransport
          B.cyclicBridge.colimitBridge.complexificationBridge.exchangeBridge.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.boundaryBridge.connection path) x)
        ((modularSpinorTransport
          B.cyclicBridge.colimitBridge.complexificationBridge.exchangeBridge.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.boundaryBridge.connection path) y)
        ((modularSpinorTransport
          B.cyclicBridge.colimitBridge.complexificationBridge.exchangeBridge.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.boundaryBridge.connection path) z) =
      canonicalSplitG2ThreeFormValue x y z := by
  have h := modularSpinor_Cl11MarkovJonesTopologicalCyclic_transport_preserves_threeForm F B.cyclicBridge path x y z
  simp_all [modularSpinorTransport]
  <;> exact h

/-- The continuous involution readout on the concrete Cl(1,1)-Cuntz colimit is
available inside the joint bridge. -/
noncomputable def cl11Cuntz_topologicalStarReadout :
    topologicalColimitObject concreteData ⟶ topologicalColimitObject concreteData :=
  topologicalStarReadout concreteData

/-- Stagewise readback of the continuous involution remains available inside the
joint bridge. -/
@[simp] theorem cl11Cuntz_topologicalStarReadout_inclusion
    (n : ℕ) (A : MatrixStage n) :
    cl11Cuntz_topologicalStarReadout (topologicalInclusion concreteData n A) =
      topologicalInclusion concreteData n A.conjTranspose :=
  topologicalStarReadout_inclusion concreteData n A

/-- The continuous involution on the concrete Cl(1,1)-Cuntz colimit remains
involutive inside the joint bridge. -/
theorem cl11Cuntz_topologicalStarReadout_involutive :
    cl11Cuntz_topologicalStarReadout ≫ cl11Cuntz_topologicalStarReadout = 𝟙 _ :=
  topologicalStarReadout_involutive concreteData

/-- The coherent finite-stage complexification still intertwines the algebraic
limit involution with the topological involution readout. -/
theorem cl11Cuntz_coherentComplexification_limitStarAddHom_compatibility
    (x : Limit) :
    coherentComplexificationColimitMap
        (coherentAlgebraicToTopological (limitStarAddHom x)) =
      cl11Cuntz_topologicalStarReadout
        (coherentComplexificationColimitMap
          (coherentAlgebraicToTopological x)) :=
  coherentComplexification_limitStarAddHom_compatibility x

end

end InfoGeometry.Canonical
