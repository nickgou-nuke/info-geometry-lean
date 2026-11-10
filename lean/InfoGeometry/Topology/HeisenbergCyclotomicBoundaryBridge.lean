/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Topology.HeisenbergCyclotomicAtlasTopological
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Heisenberg Cyclotomic Boundary Bridge

This module pairs `heisenbergBoundaryAtlasReadout` and `heisenbergCyclotomicRootReadout`
into the product readout `boundaryCyclotomicReadout`, and proves coordinate projections,
root independence of the Heisenberg boundary component, continuity, and local constancy.

- BUCKET 1 (Established Mathematical Target & Existing Owners):
  * `InfoGeometry.Topology.HeisenbergCyclotomicAtlasTopological`:
    `SixthRootParameter`, `heisenbergBoundaryAtlasReadout`,
    `heisenbergCyclotomicRootReadout`, `continuous_heisenbergBoundaryAtlasReadout`,
    `continuous_heisenbergCyclotomicRootReadout`.
- BUCKET 2 (Deconfabulation):
  * Coordinate projections, root independence, and product continuity are proved
    constructively.
- BUCKET 3 (Constructive Lean 4 Theorems Proved Here):
  * `boundaryCyclotomicReadout`.
  * `boundaryCyclotomicReadout_fst`, `boundaryCyclotomicReadout_snd`.
  * `heisenbergBoundaryAtlasReadout_root_independent`.
  * `continuous_boundaryCyclotomicReadout`,
    `isLocallyConstant_boundaryCyclotomicReadout`.
-/

namespace InfoGeometry.Topology.HeisenbergCyclotomicBoundaryBridge

open InfoGeometry.Canonical
open InfoGeometry.Topology.HeisenbergCyclotomicAtlasTopological

noncomputable section

variable {𝕜 : Type*} [Field 𝕜]

/-- The combined Heisenberg boundary / cyclotomic root readout. -/
def boundaryCyclotomicReadout (α : 𝕜) (q : SixthRootParameter) :
    InfoGeometry.Canonical.HeisenbergBoundaryAtlas.Atlas (𝕜 := 𝕜) α × ℂˣ :=
  (heisenbergBoundaryAtlasReadout (𝕜 := 𝕜) α q,
   heisenbergCyclotomicRootReadout (𝕜 := 𝕜) α q)

/-- First projection of `boundaryCyclotomicReadout α q` is `heisenbergBoundaryAtlasReadout α q`. -/
@[simp] theorem boundaryCyclotomicReadout_fst
    (α : 𝕜) (q : SixthRootParameter) :
    (boundaryCyclotomicReadout (𝕜 := 𝕜) α q).1 =
      heisenbergBoundaryAtlasReadout (𝕜 := 𝕜) α q := by
  unfold boundaryCyclotomicReadout
  exact Eq.refl _

/-- Second projection of `boundaryCyclotomicReadout α q` is `heisenbergCyclotomicRootReadout α q`. -/
@[simp] theorem boundaryCyclotomicReadout_snd
    (α : 𝕜) (q : SixthRootParameter) :
    (boundaryCyclotomicReadout (𝕜 := 𝕜) α q).2 =
      heisenbergCyclotomicRootReadout (𝕜 := 𝕜) α q := by
  unfold boundaryCyclotomicReadout
  exact Eq.refl _

/-- The Heisenberg boundary component does not vary with the sixth-root parameter `q`. -/
theorem heisenbergBoundaryAtlasReadout_root_independent
    (α : 𝕜) (q q' : SixthRootParameter) :
    heisenbergBoundaryAtlasReadout (𝕜 := 𝕜) α q =
      heisenbergBoundaryAtlasReadout (𝕜 := 𝕜) α q' := by
  unfold heisenbergBoundaryAtlasReadout
  rw [InfoGeometry.Canonical.HeisenbergCyclotomicAtlas.canonicalAtlas_heisenberg,
    InfoGeometry.Canonical.HeisenbergCyclotomicAtlas.canonicalAtlas_heisenberg]

/-- The combined boundary/cyclotomic readout is continuous via `Continuous.prodMk`. -/
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

/-- The combined readout is locally constant on the discrete sixth-root parameter space. -/
theorem isLocallyConstant_boundaryCyclotomicReadout (α : 𝕜) :
    IsLocallyConstant (boundaryCyclotomicReadout (𝕜 := 𝕜) α) := by
  unfold boundaryCyclotomicReadout
  exact IsLocallyConstant.of_discrete

end
end InfoGeometry.Topology.HeisenbergCyclotomicBoundaryBridge
