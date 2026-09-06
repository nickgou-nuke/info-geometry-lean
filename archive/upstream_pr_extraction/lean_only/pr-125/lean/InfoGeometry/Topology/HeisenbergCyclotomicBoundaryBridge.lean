import InfoGeometry.Topology.HeisenbergCyclotomicAtlasTopological

/-!
# Heisenberg cyclotomic boundary bridge

This file packages the already verified Heisenberg boundary atlas together
with the sixth-root parameter lane.  It does not identify the Heisenberg
carrier with the cyclotomic root data; it only records the product readout
and the fact that the Heisenberg boundary component is independent of the
cyclotomic parameter.
-/

namespace InfoGeometry.Topology.HeisenbergCyclotomicBoundaryBridge

open InfoGeometry.Canonical
open InfoGeometry.Topology.HeisenbergCyclotomicAtlasTopological

noncomputable section

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]

/-- The combined Heisenberg boundary / cyclotomic root readout. -/
def boundaryCyclotomicReadout (α : 𝕜) (q : SixthRootParameter) :
    InfoGeometry.Canonical.HeisenbergBoundaryAtlas.Atlas (𝕜 := 𝕜) α × ℂˣ :=
  (heisenbergBoundaryAtlasReadout (𝕜 := 𝕜) α q,
   heisenbergCyclotomicRootReadout (𝕜 := 𝕜) α q)

@[simp] theorem boundaryCyclotomicReadout_fst
    (α : 𝕜) (q : SixthRootParameter) :
    (boundaryCyclotomicReadout (𝕜 := 𝕜) α q).1 =
      heisenbergBoundaryAtlasReadout (𝕜 := 𝕜) α q := by
  rfl

@[simp] theorem boundaryCyclotomicReadout_snd
    (α : 𝕜) (q : SixthRootParameter) :
    (boundaryCyclotomicReadout (𝕜 := 𝕜) α q).2 =
      heisenbergCyclotomicRootReadout (𝕜 := 𝕜) α q := by
  rfl

/-- The Heisenberg boundary component does not vary with the sixth-root lane. -/
theorem heisenbergBoundaryAtlasReadout_root_independent
    (α : 𝕜) (q q' : SixthRootParameter) :
    heisenbergBoundaryAtlasReadout (𝕜 := 𝕜) α q =
      heisenbergBoundaryAtlasReadout (𝕜 := 𝕜) α q' := by
  rfl

/-- The combined boundary/cyclotomic readout is continuous. -/
theorem continuous_boundaryCyclotomicReadout (α : 𝕜) :
    Continuous (boundaryCyclotomicReadout (𝕜 := 𝕜) α) := by
  have h1 : Continuous (heisenbergBoundaryAtlasReadout (𝕜 := 𝕜) α) :=
    continuous_heisenbergBoundaryAtlasReadout (𝕜 := 𝕜) α
  have h2 : Continuous (heisenbergCyclotomicRootReadout (𝕜 := 𝕜) α) :=
    continuous_heisenbergCyclotomicRootReadout (𝕜 := 𝕜) α
  change Continuous (fun q : SixthRootParameter =>
    (heisenbergBoundaryAtlasReadout (𝕜 := 𝕜) α q,
      heisenbergCyclotomicRootReadout (𝕜 := 𝕜) α q))
  exact Continuous.prodMk h1 h2

/-- The combined readout is locally constant because the parameter space is discrete. -/
theorem isLocallyConstant_boundaryCyclotomicReadout (α : 𝕜) :
    IsLocallyConstant (boundaryCyclotomicReadout (𝕜 := 𝕜) α) := by
  simpa [boundaryCyclotomicReadout] using
    (IsLocallyConstant.of_discrete
      (f := boundaryCyclotomicReadout (𝕜 := 𝕜) α))
