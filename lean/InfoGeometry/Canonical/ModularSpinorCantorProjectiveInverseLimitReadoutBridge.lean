import InfoGeometry.Canonical.ModularSpinorCantorProjectiveReadoutBridge
import InfoGeometry.Canonical.CantorProjectiveLimitInverseLimitReadoutTopCat

namespace InfoGeometry.Canonical

open CategoryTheory
open CategoryTheory.Limits
open FilteredColimit.Native.Topological
open InfoGeometry.Canonical.CantorProjectiveLimit
open InfoGeometry.Canonical.CantorProjectiveReadoutBridge
open InfoGeometry.Canonical.CantorProjectiveLimitTopCat
open InfoGeometry.Canonical.CantorProjectiveLimitReadoutTopCat
open InfoGeometry.Canonical.CantorProjectiveLimitCategoricalIsoTopCat
open InfoGeometry.Canonical.CantorProjectiveLimitInverseLimitReadoutTopCat
open InfoGeometry.Canonical.UHFInductiveColimitBoundaryInverseLimit

noncomputable section

universe u

/-!
# Modular-spinor / Cantor projective inverse-limit readout bridge

This file adds the next honest node after
`ModularSpinorCantorProjectiveReadoutBridge`. The repository already owns:

* a modular-spinor / Cantor projective-readout bridge;
* a compatibility theorem between the concrete projective-limit readout and the
  categorical inverse-limit readout.

What it does not own is a theorem identifying the modular-spinor sheaf/spectrum
lane with the categorical inverse-limit boundary or proving exchange/KMS
compatibility with that inverse-limit presentation. Accordingly, this file only
packages the existing owner surfaces and re-exports the native facts already
proved in each.
-/

variable {E Sections BoundarySections Gr Open : Type*}
variable [AddCommGroup Sections] [Module ℝ Sections]
variable [AddCommGroup BoundarySections] [Module ℝ BoundarySections]
variable [TopologicalSpace Gr] [Category Open]
variable {J : Type u} [Category.{u, u} J]

/-- A joint owner for the modular-spinor/Cantor projective-readout bridge and
its categorical inverse-limit readout comparison. -/
structure ModularSpinorCantorProjectiveInverseLimitReadoutBridge
  {E Sections BoundarySections Gr Open : Type*}
  [AddCommGroup Sections] [Module ℝ Sections]
  [AddCommGroup BoundarySections] [Module ℝ BoundarySections]
  [TopologicalSpace Gr] [Category Open]
  {J : Type u} [Category.{u, u} J]
  (F : J ⥤ TopCat.{u}) where
  readoutBridge : ModularSpinorCantorProjectiveReadoutBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F

/-- The sheaf cover condition remains available inside the inverse-limit
readout bridge. -/
theorem modularSpinor_CantorProjectiveInverseLimit_monogenicSheaf_isSheafFor
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorCantorProjectiveInverseLimitReadoutBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F) :
    Presieve.IsSheafFor
      B.readoutBridge.limitBridge.sequentialBridge.starBridge.cyclicBridge.colimitBridge.complexificationBridge.exchangeBridge.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.sheafData.sections
      B.readoutBridge.limitBridge.sequentialBridge.starBridge.cyclicBridge.colimitBridge.complexificationBridge.exchangeBridge.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.sheafData.cover :=
  modularSpinor_CantorProjectiveReadout_monogenicSheaf_isSheafFor F B.readoutBridge

/-- Monogenic section membership remains available inside the inverse-limit
readout bridge. -/
theorem modularSpinor_CantorProjectiveInverseLimit_monogenicSection_mem
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorCantorProjectiveInverseLimitReadoutBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F)
  (U : Open)
  (s : B.readoutBridge.limitBridge.sequentialBridge.starBridge.cyclicBridge.colimitBridge.complexificationBridge.exchangeBridge.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.sheafData.monogenicSections U) :
    (s : B.readoutBridge.limitBridge.sequentialBridge.starBridge.cyclicBridge.colimitBridge.complexificationBridge.exchangeBridge.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.sheafData.sections.obj (Opposite.op U))
      ∈ B.readoutBridge.limitBridge.sequentialBridge.starBridge.cyclicBridge.colimitBridge.complexificationBridge.exchangeBridge.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.sheafData.monogenicSections U :=
  modularSpinor_CantorProjectiveReadout_monogenicSection_mem F B.readoutBridge U s

/-- The DN-kernel identity remains available inside the inverse-limit readout
bridge. -/
theorem modularSpinor_CantorProjectiveInverseLimit_boundary_kernel_eq_traceMonogenic
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorCantorProjectiveInverseLimitReadoutBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F) :
    LinearMap.ker
      B.readoutBridge.limitBridge.sequentialBridge.starBridge.cyclicBridge.colimitBridge.complexificationBridge.exchangeBridge.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.boundaryBridge.boundaryData.dirichletToNeumann =
      traceMonogenic B.readoutBridge.limitBridge.sequentialBridge.starBridge.cyclicBridge.colimitBridge.complexificationBridge.exchangeBridge.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.boundaryBridge.boundaryData :=
  modularSpinor_CantorProjectiveReadout_boundary_kernel_eq_traceMonogenic F B.readoutBridge

/-- Gelfand-spectrum descent remains available inside the inverse-limit readout
bridge. -/
noncomputable def modularSpinor_CantorProjectiveInverseLimit_gelfandSpectrumDescend
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorCantorProjectiveInverseLimitReadoutBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F) :
    GelfandSpectrum F ⟶ GelfandSpectrum F :=
  modularSpinor_CantorProjectiveReadout_gelfandSpectrumDescend F B.readoutBridge

@[reassoc (attr := simp)]
theorem modularSpinor_CantorProjectiveInverseLimit_gelfandSpectrum_stage
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorCantorProjectiveInverseLimitReadoutBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F)
  (j : J) :
    colimit.ι F j ≫
      modularSpinor_CantorProjectiveInverseLimit_gelfandSpectrumDescend F B =
      colimit.ι F j := by
  dsimp only [modularSpinor_CantorProjectiveInverseLimit_gelfandSpectrumDescend] at *
  exact modularSpinor_CantorProjectiveReadout_gelfandSpectrum_stage F B.readoutBridge j

/-- Modular-spinor transport still preserves the canonical three-form inside the
full inverse-limit readout bridge. -/
theorem modularSpinor_CantorProjectiveInverseLimit_transport_preserves_threeForm
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorCantorProjectiveInverseLimitReadoutBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F)
  (path : List E) (x y z : ModularSpinorCarrier) :
    canonicalSplitG2ThreeFormValue
        ((modularSpinorTransport
          B.readoutBridge.limitBridge.sequentialBridge.starBridge.cyclicBridge.colimitBridge.complexificationBridge.exchangeBridge.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.boundaryBridge.connection path) x)
        ((modularSpinorTransport
          B.readoutBridge.limitBridge.sequentialBridge.starBridge.cyclicBridge.colimitBridge.complexificationBridge.exchangeBridge.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.boundaryBridge.connection path) y)
        ((modularSpinorTransport
          B.readoutBridge.limitBridge.sequentialBridge.starBridge.cyclicBridge.colimitBridge.complexificationBridge.exchangeBridge.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.boundaryBridge.connection path) z) =
      canonicalSplitG2ThreeFormValue x y z := by
  have h := modularSpinor_CantorProjectiveReadout_transport_preserves_threeForm F B.readoutBridge path x y z
  simp_all [modularSpinorTransport]
  <;> exact h

/-- The concrete projective-limit to categorical-limit isomorphism remains
available inside the joint bridge. -/
def cantorProjective_projectiveToCategoricalLimitTopCatIso :
    TopCat.of PrefixProjectiveLimit ≅
      TopCat.of (↑(limit prefixDiagram)) :=
  projectiveToCategoricalLimitTopCatIso

/-- The concrete projective-limit readout remains available inside the joint
bridge. -/
def cantorProjective_projectiveLimitReadoutTopCatHom :
    TopCat.of PrefixProjectiveLimit ⟶ TopCat.of ℝ :=
  projectiveLimitReadoutTopCatHom

/-- The categorical inverse-limit readout remains available inside the joint
bridge. -/
def cantorProjective_inverseLimitReadoutTopCatHom :
    TopCat.of (↑(limit prefixDiagram)) ⟶ TopCat.of ℝ :=
  UHFBoundaryInverseLimitReadoutTopCat.inverseLimitReadoutTopCatHom

/-- The inverse-limit readout agrees with the concrete projective-limit readout
under the canonical topological isomorphism. -/
theorem cantorProjective_inverseLimit_readout_compatibility :
    cantorProjective_projectiveToCategoricalLimitTopCatIso.hom ≫
        cantorProjective_inverseLimitReadoutTopCatHom =
      cantorProjective_projectiveLimitReadoutTopCatHom := by
  simpa [cantorProjective_projectiveToCategoricalLimitTopCatIso,
    cantorProjective_inverseLimitReadoutTopCatHom,
    cantorProjective_projectiveLimitReadoutTopCatHom] using
    projective_inverseLimit_readout_compatibility

end

end InfoGeometry.Canonical
