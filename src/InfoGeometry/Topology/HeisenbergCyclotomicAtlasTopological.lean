/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.HeisenbergCyclotomicAtlas

/-!
# Topological Readout for the Heisenberg Cyclotomic Atlas

This module defines the discrete parameter subtype `SixthRootParameter` of sixth roots
of unity in `ℂˣ`, extracts the Heisenberg boundary atlas readout and sixth-root readout
from `HeisenbergCyclotomicAtlas.canonicalAtlas`, and proves their evaluation, continuity,
and local constancy properties.

- BUCKET 1 (Established Mathematical Target & Existing Owners):
  * `InfoGeometry.Canonical.HeisenbergCyclotomicAtlas`: `Atlas`, `canonicalAtlas`,
    `canonicalAtlas_heisenberg`, `canonicalAtlas_sixthRoot`.
- BUCKET 2 (Deconfabulation):
  * Readout evaluations and continuity theorems are proved via explicit unfolding and
    discrete-topology lemmas.
- BUCKET 3 (Constructive Lean 4 Theorems Proved Here):
  * `SixthRootParameter`: subtype `{p : ℂˣ // (p : ℂ) ^ 6 = 1}`.
  * `heisenbergBoundaryAtlasReadout`, `heisenbergCyclotomicRootReadout`.
  * `heisenbergBoundaryAtlasReadout_apply`, `heisenbergCyclotomicRootReadout_apply`.
  * `continuous_heisenbergBoundaryAtlasReadout`, `continuous_heisenbergCyclotomicRootReadout`,
    `isLocallyConstant_heisenbergBoundaryAtlasReadout`,
    `isLocallyConstant_heisenbergCyclotomicRootReadout`.
-/

namespace InfoGeometry.Topology.HeisenbergCyclotomicAtlasTopological

open InfoGeometry.Canonical

noncomputable section

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]

/-- The parameter subtype for the cyclotomic sixth-root lane `{p : ℂˣ // (p : ℂ) ^ 6 = 1}`. -/
def SixthRootParameter :=
  {p : ℂˣ // (p : ℂ) ^ 6 = 1}

instance sixthRootParameterTopologicalSpace :
    TopologicalSpace SixthRootParameter := ⊥

instance sixthRootParameterDiscreteTopology :
    DiscreteTopology SixthRootParameter := DiscreteTopology.mk (Eq.refl _)

instance heisenbergBoundaryAtlasTopologicalSpace (α : 𝕜) :
    TopologicalSpace
      (InfoGeometry.Canonical.HeisenbergBoundaryAtlas.Atlas (𝕜 := 𝕜) α) := ⊥

/-- Heisenberg boundary component of `canonicalAtlas` as a function of `SixthRootParameter`. -/
def heisenbergBoundaryAtlasReadout (α : 𝕜) (q : SixthRootParameter) :
    InfoGeometry.Canonical.HeisenbergBoundaryAtlas.Atlas (𝕜 := 𝕜) α :=
  (InfoGeometry.Canonical.HeisenbergCyclotomicAtlas.canonicalAtlas
      (𝕜 := 𝕜) α q.1 q.2).heisenberg

/-- Cyclotomic sixth-root component of `canonicalAtlas` as a function of `SixthRootParameter`. -/
def heisenbergCyclotomicRootReadout (α : 𝕜) (q : SixthRootParameter) : ℂˣ :=
  (InfoGeometry.Canonical.HeisenbergCyclotomicAtlas.canonicalAtlas
      (𝕜 := 𝕜) α q.1 q.2).sixthRoot

/-- Explicit evaluation of `heisenbergBoundaryAtlasReadout α q`. -/
@[simp] theorem heisenbergBoundaryAtlasReadout_apply
    (α : 𝕜) (q : SixthRootParameter) :
    heisenbergBoundaryAtlasReadout α q =
      (InfoGeometry.Canonical.HeisenbergCyclotomicAtlas.canonicalAtlas
          (𝕜 := 𝕜) α q.1 q.2).heisenberg := by
  unfold heisenbergBoundaryAtlasReadout
  exact Eq.refl _

/-- Explicit evaluation of `heisenbergCyclotomicRootReadout α q`. -/
@[simp] theorem heisenbergCyclotomicRootReadout_apply
    (α : 𝕜) (q : SixthRootParameter) :
    heisenbergCyclotomicRootReadout α q =
      (InfoGeometry.Canonical.HeisenbergCyclotomicAtlas.canonicalAtlas
          (𝕜 := 𝕜) α q.1 q.2).sixthRoot := by
  unfold heisenbergCyclotomicRootReadout
  exact Eq.refl _

/-- The Heisenberg boundary readout is continuous on the discrete parameter set. -/
theorem continuous_heisenbergBoundaryAtlasReadout (α : 𝕜) :
    Continuous (heisenbergBoundaryAtlasReadout α) := by
  unfold heisenbergBoundaryAtlasReadout
  exact continuous_of_discreteTopology

/-- The cyclotomic-root readout is continuous on the discrete parameter set. -/
theorem continuous_heisenbergCyclotomicRootReadout (α : 𝕜) :
    Continuous (heisenbergCyclotomicRootReadout α) := by
  unfold heisenbergCyclotomicRootReadout
  exact continuous_of_discreteTopology

/-- The Heisenberg boundary readout is locally constant on the discrete parameter set. -/
theorem isLocallyConstant_heisenbergBoundaryAtlasReadout (α : 𝕜) :
    IsLocallyConstant (heisenbergBoundaryAtlasReadout α) := by
  intro s
  exact isOpen_discrete _

/-- The cyclotomic-root readout is locally constant on the discrete parameter set. -/
theorem isLocallyConstant_heisenbergCyclotomicRootReadout (α : 𝕜) :
    IsLocallyConstant (heisenbergCyclotomicRootReadout α) := by
  intro s
  exact isOpen_discrete _

end
end InfoGeometry.Topology.HeisenbergCyclotomicAtlasTopological
