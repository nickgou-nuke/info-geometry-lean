import InfoGeometry.Canonical.ModularSpinorCantorProjectiveBranchReadoutBridge
import InfoGeometry.Canonical.CantorProjectiveBernoulliMeasure

namespace InfoGeometry.Canonical

open CategoryTheory
open CategoryTheory.Limits
open FilteredColimit.Native.Topological
open MeasureTheory
open scoped ENNReal
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.CantorProjectiveLimit
open InfoGeometry.Canonical.CantorProjectiveLimit.PrefixProjectiveLimit
open InfoGeometry.Canonical.CantorProjectiveBernoulliMeasure
open InfoGeometry.Canonical.RindlerMobiusCantorFiniteBridge

noncomputable section

universe u

/-!
# Modular-spinor / Cantor projective Bernoulli-measure bridge

This file adds the next honest node after
`ModularSpinorCantorProjectiveBranchReadoutBridge`. The repository already owns:

* a modular-spinor / Cantor projective branch-readout bridge;
* a Bernoulli/projective-limit measure package with prefix-fiber masses,
  readout control, and Tomita symmetrization facts.

What it does not own is a theorem identifying the modular-spinor sheaf/spectrum
lane with the Bernoulli measure or proving exchange/KMS compatibility with that
measure package. Accordingly, this file only packages the existing owner
surfaces and re-exports the native facts already proved in each.
-/

variable {E Sections BoundarySections Gr Open : Type*}
variable [AddCommGroup Sections] [Module ℝ Sections]
variable [AddCommGroup BoundarySections] [Module ℝ BoundarySections]
variable [TopologicalSpace Gr] [Category Open]
variable {J : Type u} [Category.{u, u} J]

/-- A joint owner for the modular-spinor/Cantor projective branch-readout bridge
and the Bernoulli/projective-limit measure lane. -/
structure ModularSpinorCantorProjectiveBernoulliMeasureBridge
  {E Sections BoundarySections Gr Open : Type*}
  [AddCommGroup Sections] [Module ℝ Sections]
  [AddCommGroup BoundarySections] [Module ℝ BoundarySections]
  [TopologicalSpace Gr] [Category Open]
  {J : Type u} [Category.{u, u} J]
  (F : J ⥤ TopCat.{u}) where
  branchReadoutBridge : ModularSpinorCantorProjectiveBranchReadoutBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F

/-- The sheaf cover condition remains available inside the Bernoulli-measure
bridge. -/
theorem modularSpinor_CantorProjectiveBernoulli_monogenicSheaf_isSheafFor
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorCantorProjectiveBernoulliMeasureBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F) :
    Presieve.IsSheafFor
      B.branchReadoutBridge.inverseLimitReadoutBridge.readoutBridge.limitBridge.sequentialBridge.starBridge.cyclicBridge.colimitBridge.complexificationBridge.exchangeBridge.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.sheafData.sections
      B.branchReadoutBridge.inverseLimitReadoutBridge.readoutBridge.limitBridge.sequentialBridge.starBridge.cyclicBridge.colimitBridge.complexificationBridge.exchangeBridge.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.sheafData.cover :=
  modularSpinor_CantorProjectiveBranchReadout_monogenicSheaf_isSheafFor F B.branchReadoutBridge

/-- Monogenic section membership remains available inside the Bernoulli-measure
bridge. -/
theorem modularSpinor_CantorProjectiveBernoulli_monogenicSection_mem
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorCantorProjectiveBernoulliMeasureBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F)
  (U : Open)
  (s : B.branchReadoutBridge.inverseLimitReadoutBridge.readoutBridge.limitBridge.sequentialBridge.starBridge.cyclicBridge.colimitBridge.complexificationBridge.exchangeBridge.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.sheafData.monogenicSections U) :
    (s : B.branchReadoutBridge.inverseLimitReadoutBridge.readoutBridge.limitBridge.sequentialBridge.starBridge.cyclicBridge.colimitBridge.complexificationBridge.exchangeBridge.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.sheafData.sections.obj (Opposite.op U))
      ∈ B.branchReadoutBridge.inverseLimitReadoutBridge.readoutBridge.limitBridge.sequentialBridge.starBridge.cyclicBridge.colimitBridge.complexificationBridge.exchangeBridge.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.sheafData.monogenicSections U :=
  modularSpinor_CantorProjectiveBranchReadout_monogenicSection_mem F B.branchReadoutBridge U s

/-- The DN-kernel identity remains available inside the Bernoulli-measure
bridge. -/
theorem modularSpinor_CantorProjectiveBernoulli_boundary_kernel_eq_traceMonogenic
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorCantorProjectiveBernoulliMeasureBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F) :
    LinearMap.ker
      B.branchReadoutBridge.inverseLimitReadoutBridge.readoutBridge.limitBridge.sequentialBridge.starBridge.cyclicBridge.colimitBridge.complexificationBridge.exchangeBridge.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.boundaryBridge.boundaryData.dirichletToNeumann =
      traceMonogenic B.branchReadoutBridge.inverseLimitReadoutBridge.readoutBridge.limitBridge.sequentialBridge.starBridge.cyclicBridge.colimitBridge.complexificationBridge.exchangeBridge.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.boundaryBridge.boundaryData :=
  modularSpinor_CantorProjectiveBranchReadout_boundary_kernel_eq_traceMonogenic F B.branchReadoutBridge

/-- Gelfand-spectrum descent remains available inside the Bernoulli-measure
bridge. -/
noncomputable def modularSpinor_CantorProjectiveBernoulli_gelfandSpectrumDescend
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorCantorProjectiveBernoulliMeasureBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F) :
    GelfandSpectrum F ⟶ GelfandSpectrum F :=
  modularSpinor_CantorProjectiveBranchReadout_gelfandSpectrumDescend F B.branchReadoutBridge

@[reassoc (attr := simp)]
theorem modularSpinor_CantorProjectiveBernoulli_gelfandSpectrum_stage
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorCantorProjectiveBernoulliMeasureBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F)
  (j : J) :
    colimit.ι F j ≫
      modularSpinor_CantorProjectiveBernoulli_gelfandSpectrumDescend F B =
      colimit.ι F j := by
  dsimp only [modularSpinor_CantorProjectiveBernoulli_gelfandSpectrumDescend] at *
  exact modularSpinor_CantorProjectiveBranchReadout_gelfandSpectrum_stage F B.branchReadoutBridge j

/-- Modular-spinor transport still preserves the canonical three-form inside the
full Bernoulli-measure bridge. -/
theorem modularSpinor_CantorProjectiveBernoulli_transport_preserves_threeForm
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorCantorProjectiveBernoulliMeasureBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F)
  (path : List E) (x y z : ModularSpinorCarrier) :
    canonicalSplitG2ThreeFormValue
        ((modularSpinorTransport
          B.branchReadoutBridge.inverseLimitReadoutBridge.readoutBridge.limitBridge.sequentialBridge.starBridge.cyclicBridge.colimitBridge.complexificationBridge.exchangeBridge.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.boundaryBridge.connection path) x)
        ((modularSpinorTransport
          B.branchReadoutBridge.inverseLimitReadoutBridge.readoutBridge.limitBridge.sequentialBridge.starBridge.cyclicBridge.colimitBridge.complexificationBridge.exchangeBridge.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.boundaryBridge.connection path) y)
        ((modularSpinorTransport
          B.branchReadoutBridge.inverseLimitReadoutBridge.readoutBridge.limitBridge.sequentialBridge.starBridge.cyclicBridge.colimitBridge.complexificationBridge.exchangeBridge.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.boundaryBridge.connection path) z) =
      canonicalSplitG2ThreeFormValue x y z := by
  have h := modularSpinor_CantorProjectiveBranchReadout_transport_preserves_threeForm F B.branchReadoutBridge path x y z
  simp_all [modularSpinorTransport]
  <;> exact h

/-- The Bernoulli/projective-limit measure remains available inside the joint
bridge. -/
def cantorProjective_projectiveLimitMeasure : Measure PrefixProjectiveLimit :=
  projectiveLimitMeasure

/-- Prefix fibers keep the expected Bernoulli mass. -/
theorem cantorProjective_projectiveLimitMeasure_apply_prefix_fiber
    (N : ℕ) (b : BitWord N) :
    cantorProjective_projectiveLimitMeasure {q : PrefixProjectiveLimit | q.π N = b} =
      (1 / 2 : ℝ≥0∞) ^ N :=
  projectiveLimitMeasure_apply_prefix_fiber N b

/-- Prefix fibers satisfy the native mass-and-readout control package. -/
theorem cantorProjective_prefix_fiber_mass_and_readout_control
    (N : ℕ) (b : BitWord N) :
    cantorProjective_projectiveLimitMeasure {q : PrefixProjectiveLimit | q.π N = b} =
        (1 / 2 : ℝ≥0∞) ^ N ∧
      ∀ {p q : PrefixProjectiveLimit},
        p.π N = b → q.π N = b →
          |CantorBoundaryReadoutBounds.realBinaryReadout (toCantor p) -
              CantorBoundaryReadoutBounds.realBinaryReadout (toCantor q)| ≤
            (1 / 2 : ℝ) ^ N :=
  projectiveLimit_prefix_fiber_mass_and_readout_control N b

/-- The Tomita image of each prefix fiber preserves its Bernoulli mass. -/
theorem cantorProjective_tomita_measure_image_prefix_fiber
    (N : ℕ) (b : BitWord N) :
    cantorProjective_projectiveLimitMeasure
        (tomitaProjectiveLimit '' {q : PrefixProjectiveLimit | q.π N = b}) =
      cantorProjective_projectiveLimitMeasure {q : PrefixProjectiveLimit | q.π N = b} := by
  simpa [cantorProjective_projectiveLimitMeasure] using
    tomita_measure_image_prefix_fiber N b

/-- Prefix-fiber Bernoulli mass splits additively over the two successor fibers. -/
theorem cantorProjective_projectiveLimitMeasure_prefix_successor_additive
    (N : ℕ) (b : BitWord N) :
    cantorProjective_projectiveLimitMeasure {q : PrefixProjectiveLimit | q.π N = b} =
      cantorProjective_projectiveLimitMeasure
          {q : PrefixProjectiveLimit | q.π (N + 1) = extendSucc N b false} +
      cantorProjective_projectiveLimitMeasure
          {q : PrefixProjectiveLimit | q.π (N + 1) = extendSucc N b true} :=
  projectiveLimitMeasure_prefix_successor_additive N b

end

end InfoGeometry.Canonical
