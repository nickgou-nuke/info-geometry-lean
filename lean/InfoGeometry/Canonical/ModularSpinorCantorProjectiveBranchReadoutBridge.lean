import InfoGeometry.Canonical.ModularSpinorCantorProjectiveInverseLimitReadoutBridge
import InfoGeometry.Canonical.CantorProjectiveLimitBranchReadoutTopCat

namespace InfoGeometry.Canonical

open CategoryTheory
open CategoryTheory.Limits
open FilteredColimit.Native.Topological
open InfoGeometry.Canonical.CantorProjectiveLimit
open InfoGeometry.Canonical.CantorProjectiveReadoutBridge
open InfoGeometry.Canonical.CantorProjectiveLimitTopCat
open InfoGeometry.Canonical.CantorProjectiveLimitReadoutTopCat
open InfoGeometry.Canonical.CantorProjectiveLimitBranchTopCat
open InfoGeometry.Canonical.CantorProjectiveLimitBranchReadoutTopCat
open InfoGeometry.Canonical.UHFInductiveColimitBoundaryInverseLimit
open InfoGeometry.Canonical.CantorBoundaryReadoutTopCat

noncomputable section

universe u

/-!
# Modular-spinor / Cantor projective branch-readout bridge

This file adds the next honest node after
`ModularSpinorCantorProjectiveInverseLimitReadoutBridge`. The repository already owns:

* a modular-spinor / Cantor projective inverse-limit readout bridge;
* a branch/readout recursion on the concrete projective-limit carrier.

What it does not own is a theorem identifying the modular-spinor sheaf/spectrum
lane with the branch-shift structure or proving exchange/KMS compatibility with
the branch-affine readout law. Accordingly, this file only packages the existing
owner surfaces and re-exports the native facts already proved in each.
-/

variable {E Sections BoundarySections Gr Open : Type*}
variable [AddCommGroup Sections] [Module ℝ Sections]
variable [AddCommGroup BoundarySections] [Module ℝ BoundarySections]
variable [TopologicalSpace Gr] [Category Open]
variable {J : Type u} [Category.{u, u} J]

/-- A joint owner for the modular-spinor/Cantor projective inverse-limit
readout bridge and its branch-readout recursion. -/
structure ModularSpinorCantorProjectiveBranchReadoutBridge
  {E Sections BoundarySections Gr Open : Type*}
  [AddCommGroup Sections] [Module ℝ Sections]
  [AddCommGroup BoundarySections] [Module ℝ BoundarySections]
  [TopologicalSpace Gr] [Category Open]
  {J : Type u} [Category.{u, u} J]
  (F : J ⥤ TopCat.{u}) where
  inverseLimitReadoutBridge : ModularSpinorCantorProjectiveInverseLimitReadoutBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F

/-- The sheaf cover condition remains available inside the branch-readout
bridge. -/
theorem modularSpinor_CantorProjectiveBranchReadout_monogenicSheaf_isSheafFor
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorCantorProjectiveBranchReadoutBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F) :
    Presieve.IsSheafFor
      B.inverseLimitReadoutBridge.readoutBridge.limitBridge.sequentialBridge.starBridge.cyclicBridge.colimitBridge.complexificationBridge.exchangeBridge.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.sheafData.sections
      B.inverseLimitReadoutBridge.readoutBridge.limitBridge.sequentialBridge.starBridge.cyclicBridge.colimitBridge.complexificationBridge.exchangeBridge.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.sheafData.cover :=
  modularSpinor_CantorProjectiveInverseLimit_monogenicSheaf_isSheafFor F B.inverseLimitReadoutBridge

/-- Monogenic section membership remains available inside the branch-readout
bridge. -/
theorem modularSpinor_CantorProjectiveBranchReadout_monogenicSection_mem
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorCantorProjectiveBranchReadoutBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F)
  (U : Open)
  (s : B.inverseLimitReadoutBridge.readoutBridge.limitBridge.sequentialBridge.starBridge.cyclicBridge.colimitBridge.complexificationBridge.exchangeBridge.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.sheafData.monogenicSections U) :
    (s : B.inverseLimitReadoutBridge.readoutBridge.limitBridge.sequentialBridge.starBridge.cyclicBridge.colimitBridge.complexificationBridge.exchangeBridge.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.sheafData.sections.obj (Opposite.op U))
      ∈ B.inverseLimitReadoutBridge.readoutBridge.limitBridge.sequentialBridge.starBridge.cyclicBridge.colimitBridge.complexificationBridge.exchangeBridge.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.sheafData.monogenicSections U :=
  modularSpinor_CantorProjectiveInverseLimit_monogenicSection_mem F B.inverseLimitReadoutBridge U s

/-- The DN-kernel identity remains available inside the branch-readout bridge. -/
theorem modularSpinor_CantorProjectiveBranchReadout_boundary_kernel_eq_traceMonogenic
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorCantorProjectiveBranchReadoutBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F) :
    LinearMap.ker
      B.inverseLimitReadoutBridge.readoutBridge.limitBridge.sequentialBridge.starBridge.cyclicBridge.colimitBridge.complexificationBridge.exchangeBridge.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.boundaryBridge.boundaryData.dirichletToNeumann =
      traceMonogenic B.inverseLimitReadoutBridge.readoutBridge.limitBridge.sequentialBridge.starBridge.cyclicBridge.colimitBridge.complexificationBridge.exchangeBridge.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.boundaryBridge.boundaryData :=
  modularSpinor_CantorProjectiveInverseLimit_boundary_kernel_eq_traceMonogenic F B.inverseLimitReadoutBridge

/-- Gelfand-spectrum descent remains available inside the branch-readout
bridge. -/
noncomputable def modularSpinor_CantorProjectiveBranchReadout_gelfandSpectrumDescend
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorCantorProjectiveBranchReadoutBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F) :
    GelfandSpectrum F ⟶ GelfandSpectrum F :=
  modularSpinor_CantorProjectiveInverseLimit_gelfandSpectrumDescend F B.inverseLimitReadoutBridge

@[reassoc (attr := simp)]
theorem modularSpinor_CantorProjectiveBranchReadout_gelfandSpectrum_stage
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorCantorProjectiveBranchReadoutBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F)
  (j : J) :
    colimit.ι F j ≫
      modularSpinor_CantorProjectiveBranchReadout_gelfandSpectrumDescend F B =
      colimit.ι F j := by
  dsimp only [modularSpinor_CantorProjectiveBranchReadout_gelfandSpectrumDescend] at *
  exact modularSpinor_CantorProjectiveInverseLimit_gelfandSpectrum_stage F B.inverseLimitReadoutBridge j

/-- Modular-spinor transport still preserves the canonical three-form inside the
full branch-readout bridge. -/
theorem modularSpinor_CantorProjectiveBranchReadout_transport_preserves_threeForm
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorCantorProjectiveBranchReadoutBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F)
  (path : List E) (x y z : ModularSpinorCarrier) :
    canonicalSplitG2ThreeFormValue
        ((modularSpinorTransport
          B.inverseLimitReadoutBridge.readoutBridge.limitBridge.sequentialBridge.starBridge.cyclicBridge.colimitBridge.complexificationBridge.exchangeBridge.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.boundaryBridge.connection path) x)
        ((modularSpinorTransport
          B.inverseLimitReadoutBridge.readoutBridge.limitBridge.sequentialBridge.starBridge.cyclicBridge.colimitBridge.complexificationBridge.exchangeBridge.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.boundaryBridge.connection path) y)
        ((modularSpinorTransport
          B.inverseLimitReadoutBridge.readoutBridge.limitBridge.sequentialBridge.starBridge.cyclicBridge.colimitBridge.complexificationBridge.exchangeBridge.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.boundaryBridge.connection path) z) =
      canonicalSplitG2ThreeFormValue x y z := by
  have h := modularSpinor_CantorProjectiveInverseLimit_transport_preserves_threeForm F B.inverseLimitReadoutBridge path x y z
  simp_all [modularSpinorTransport]
  <;> exact h

/-- The concrete projective-limit branch shift remains available inside the
joint bridge. -/
def cantorProjective_projectivePrependBitTopCatHom (b : Bool) :
    TopCat.of PrefixProjectiveLimit ⟶ TopCat.of PrefixProjectiveLimit :=
  projectivePrependBitTopCatHom b

/-- The projective-limit branch/readout affine square remains available inside
the joint bridge. -/
theorem cantorProjective_projective_branch_readout_square (b : Bool) :
    cantorProjective_projectivePrependBitTopCatHom b ≫
      cantorProjective_projectiveLimitReadoutTopCatHom =
    cantorProjective_projectiveLimitReadoutTopCatHom ≫
      CantorBoundaryReadoutTopCat.branchAffineTopCatHom b :=
  projective_branch_readout_square b

end

end InfoGeometry.Canonical
