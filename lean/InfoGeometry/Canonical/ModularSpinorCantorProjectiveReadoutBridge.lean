import InfoGeometry.Canonical.ModularSpinorCantorCl11LimitBridge
import InfoGeometry.Canonical.CantorProjectiveReadoutBridge

namespace InfoGeometry.Canonical

open CategoryTheory
open CategoryTheory.Limits
open FilteredColimit.Native.Topological
open InfoGeometry.Canonical.CantorProjectiveLimit
open InfoGeometry.Canonical.CantorProjectiveReadoutBridge
open InfoGeometry.Canonical.CantorCl11Limit
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.FractalCantorCliffordFockBridge
open InfoGeometry.Canonical.CantorProjectiveLimit.PrefixProjectiveLimit
open InfoGeometry.Canonical.CantorBoundaryReadoutBounds

noncomputable section

universe u

/-!
# Modular-spinor / Cantor projective-readout bridge

This file adds the next honest node after
`ModularSpinorCantorCl11LimitBridge`. The repository already owns:

* a modular-spinor / Cantor-Cl(1,1) direct-limit bridge;
* a genuine Cantor projective-limit / prefix-readout bridge.

What it does not own is a theorem identifying the modular-spinor sheaf/spectrum
lane with the projective-limit boundary or proving exchange/KMS compatibility
with that boundary readout. Accordingly, this file only packages the existing
owner surfaces and re-exports the native facts already proved in each.
-/

variable {E Sections BoundarySections Gr Open : Type*}
variable [AddCommGroup Sections] [Module ℝ Sections]
variable [AddCommGroup BoundarySections] [Module ℝ BoundarySections]
variable [TopologicalSpace Gr] [Category Open]
variable {J : Type u} [Category.{u, u} J]

/-- A joint owner for the modular-spinor/Cantor-Cl(1,1) limit bridge and the
Cantor projective-readout lane. -/
structure ModularSpinorCantorProjectiveReadoutBridge
  {E Sections BoundarySections Gr Open : Type*}
  [AddCommGroup Sections] [Module ℝ Sections]
  [AddCommGroup BoundarySections] [Module ℝ BoundarySections]
  [TopologicalSpace Gr] [Category Open]
  {J : Type u} [Category.{u, u} J]
  (F : J ⥤ TopCat.{u}) where
  limitBridge : ModularSpinorCantorCl11LimitBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F

/-- The sheaf cover condition remains available inside the projective-readout
bridge. -/
theorem modularSpinor_CantorProjectiveReadout_monogenicSheaf_isSheafFor
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorCantorProjectiveReadoutBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F) :
    Presieve.IsSheafFor
      B.limitBridge.sequentialBridge.starBridge.cyclicBridge.colimitBridge.complexificationBridge.exchangeBridge.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.sheafData.sections
      B.limitBridge.sequentialBridge.starBridge.cyclicBridge.colimitBridge.complexificationBridge.exchangeBridge.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.sheafData.cover :=
  modularSpinor_CantorCl11Limit_monogenicSheaf_isSheafFor F B.limitBridge

/-- Monogenic section membership remains available inside the projective-readout
bridge. -/
theorem modularSpinor_CantorProjectiveReadout_monogenicSection_mem
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorCantorProjectiveReadoutBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F)
  (U : Open)
  (s : B.limitBridge.sequentialBridge.starBridge.cyclicBridge.colimitBridge.complexificationBridge.exchangeBridge.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.sheafData.monogenicSections U) :
    (s : B.limitBridge.sequentialBridge.starBridge.cyclicBridge.colimitBridge.complexificationBridge.exchangeBridge.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.sheafData.sections.obj (Opposite.op U))
      ∈ B.limitBridge.sequentialBridge.starBridge.cyclicBridge.colimitBridge.complexificationBridge.exchangeBridge.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.sheafData.monogenicSections U :=
  modularSpinor_CantorCl11Limit_monogenicSection_mem F B.limitBridge U s

/-- The DN-kernel identity remains available inside the projective-readout
bridge. -/
theorem modularSpinor_CantorProjectiveReadout_boundary_kernel_eq_traceMonogenic
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorCantorProjectiveReadoutBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F) :
    LinearMap.ker
      B.limitBridge.sequentialBridge.starBridge.cyclicBridge.colimitBridge.complexificationBridge.exchangeBridge.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.boundaryBridge.boundaryData.dirichletToNeumann =
      traceMonogenic B.limitBridge.sequentialBridge.starBridge.cyclicBridge.colimitBridge.complexificationBridge.exchangeBridge.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.boundaryBridge.boundaryData :=
  modularSpinor_CantorCl11Limit_boundary_kernel_eq_traceMonogenic F B.limitBridge

/-- Gelfand-spectrum descent remains available inside the projective-readout
bridge. -/
noncomputable def modularSpinor_CantorProjectiveReadout_gelfandSpectrumDescend
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorCantorProjectiveReadoutBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F) :
    GelfandSpectrum F ⟶ GelfandSpectrum F :=
  modularSpinor_CantorCl11Limit_gelfandSpectrumDescend F B.limitBridge

@[reassoc (attr := simp)]
theorem modularSpinor_CantorProjectiveReadout_gelfandSpectrum_stage
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorCantorProjectiveReadoutBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F)
  (j : J) :
    colimit.ι F j ≫
      modularSpinor_CantorProjectiveReadout_gelfandSpectrumDescend F B =
      colimit.ι F j := by
  dsimp only [modularSpinor_CantorProjectiveReadout_gelfandSpectrumDescend] at *
  exact modularSpinor_CantorCl11Limit_gelfandSpectrum_stage F B.limitBridge j

/-- Modular-spinor transport still preserves the canonical three-form inside the
full projective-readout bridge. -/
theorem modularSpinor_CantorProjectiveReadout_transport_preserves_threeForm
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorCantorProjectiveReadoutBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F)
  (path : List E) (x y z : ModularSpinorCarrier) :
    canonicalSplitG2ThreeFormValue
        ((modularSpinorTransport
          B.limitBridge.sequentialBridge.starBridge.cyclicBridge.colimitBridge.complexificationBridge.exchangeBridge.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.boundaryBridge.connection path) x)
        ((modularSpinorTransport
          B.limitBridge.sequentialBridge.starBridge.cyclicBridge.colimitBridge.complexificationBridge.exchangeBridge.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.boundaryBridge.connection path) y)
        ((modularSpinorTransport
          B.limitBridge.sequentialBridge.starBridge.cyclicBridge.colimitBridge.complexificationBridge.exchangeBridge.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.boundaryBridge.connection path) z) =
      canonicalSplitG2ThreeFormValue x y z := by
  have h := modularSpinor_CantorCl11Limit_transport_preserves_threeForm F B.limitBridge path x y z
  simp_all [modularSpinorTransport]
  <;> exact h

/-- The finite prefix readout from the projective limit remains available
inside the joint bridge. -/
def cantorProjective_finitePrefixReadoutFn {n : ℕ} (b : BitWord n) : ℝ :=
  finitePrefixReadoutFn b

/-- The bit-word prefix list equivalence remains available inside the joint
bridge. -/
theorem cantorProjective_bitWordPrefix_list_eq
  (n : ℕ) (x : UHFInductiveColimitBoundary.CantorBoundary) :
    List.ofFn (UHFInductiveColimitBoundary.boundaryPrefix n x) =
      FractalCantorCliffordFockBridge.boundaryPrefix n x :=
  bitWordPrefix_list_eq n x

/-- The projective-readout prefix-tail decomposition remains available inside
the joint bridge. -/
theorem cantorProjective_projective_readout_prefix_tail
  (p : PrefixProjectiveLimit) (N : ℕ) :
    realBinaryReadout
      (PrefixProjectiveLimit.toCantor p) =
    cantorProjective_finitePrefixReadoutFn (π N p) +
      (1 / 2 : ℝ) ^ N *
        realBinaryReadout
          (boundaryIterateTail N (PrefixProjectiveLimit.toCantor p)) :=
  projective_readout_prefix_tail p N

end

end InfoGeometry.Canonical
