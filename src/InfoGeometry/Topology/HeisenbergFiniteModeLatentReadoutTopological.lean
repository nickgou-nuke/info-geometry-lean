/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.HeisenbergFiniteModeCyclotomicTopological
import InfoGeometry.Topology.CyclotomicLatentQuotientTopological

/-!
# Stage-Wise Latent Readout for Finite Heisenberg Modes

This module sends a sixth-root parameter and finite Heisenberg basis index
`(q, i) : SixthRootParameter × Option ℤ` to the cyclotomic latent quotient
`LatentQuotient`, defines the stage image `heisenbergFiniteModeStageLatentImage`,
and proves coordinate projections, continuity, local constancy, and stage
monotonicity.

- BUCKET 1 (Established Mathematical Target & Existing Owners):
  * `InfoGeometry.Topology.HeisenbergFiniteModeCyclotomicTopological`:
    `heisenbergBasisCyclotomicDegree`.
  * `InfoGeometry.Topology.CyclotomicLatentQuotientTopological`:
    `LatentQuotient`, `effectiveCubeRootParameter`.
- BUCKET 2 (Deconfabulation):
  * All coordinate projections, continuity, and stage-image monotonicity theorems
    are proved constructively.
- BUCKET 3 (Constructive Lean 4 Theorems Proved Here):
  * `heisenbergFiniteModeLatentReadout`, `heisenbergFiniteModeStageLatentImage`.
  * `heisenbergFiniteModeLatentReadout_root`, `heisenbergFiniteModeLatentReadout_degree`,
    `heisenbergFiniteModeLatentReadout_zero_residue`.
  * `continuous_heisenbergFiniteModeLatentReadout`,
    `isLocallyConstant_heisenbergFiniteModeLatentReadout`.
  * `heisenbergFiniteModeStageLatentImage_mono`,
    `heisenbergFiniteModeStageLatentImage_degree_mem`.
-/

namespace InfoGeometry.Topology.HeisenbergFiniteModeLatentReadoutTopological

open InfoGeometry.Topology.HeisenbergFiniteModeCyclotomicTopological
open InfoGeometry.Topology.HeisenbergCyclotomicAtlasTopological
open InfoGeometry.Topology.CyclotomicLatentQuotientTopological

noncomputable section

/-- Latent label of a Heisenberg basis index at a chosen sixth-root parameter. -/
def heisenbergFiniteModeLatentReadout
    (p : SixthRootParameter × Option ℤ) : LatentQuotient :=
  (effectiveCubeRootParameter p.1,
    (heisenbergBasisCyclotomicDegree p.2, 0))

/-- Effective cubic-root component of `heisenbergFiniteModeLatentReadout p`. -/
@[simp] theorem heisenbergFiniteModeLatentReadout_root
    (p : SixthRootParameter × Option ℤ) :
    (heisenbergFiniteModeLatentReadout p).1 =
      effectiveCubeRootParameter p.1 := by
  unfold heisenbergFiniteModeLatentReadout
  exact Eq.refl _

/-- Cyclotomic mode-degree component of `heisenbergFiniteModeLatentReadout p`. -/
@[simp] theorem heisenbergFiniteModeLatentReadout_degree
    (p : SixthRootParameter × Option ℤ) :
    (heisenbergFiniteModeLatentReadout p).2.1 =
      heisenbergBasisCyclotomicDegree p.2 := by
  unfold heisenbergFiniteModeLatentReadout
  exact Eq.refl _

/-- Second Weyl residue coordinate of `heisenbergFiniteModeLatentReadout p` is zero. -/
@[simp] theorem heisenbergFiniteModeLatentReadout_zero_residue
    (p : SixthRootParameter × Option ℤ) :
    (heisenbergFiniteModeLatentReadout p).2.2 = 0 := by
  unfold heisenbergFiniteModeLatentReadout
  exact Eq.refl _

/-- Continuity of `heisenbergFiniteModeLatentReadout` on the discrete parameter product. -/
theorem continuous_heisenbergFiniteModeLatentReadout :
    Continuous heisenbergFiniteModeLatentReadout := by
  unfold heisenbergFiniteModeLatentReadout
  exact continuous_of_discreteTopology

/-- Local constancy of `heisenbergFiniteModeLatentReadout` on the discrete parameter product. -/
theorem isLocallyConstant_heisenbergFiniteModeLatentReadout :
    IsLocallyConstant heisenbergFiniteModeLatentReadout := by
  unfold heisenbergFiniteModeLatentReadout
  exact IsLocallyConstant.of_discrete

/-- Latent labels visible from a finite mode stage `s` at a fixed root parameter `q`. -/
def heisenbergFiniteModeStageLatentImage
    (q : SixthRootParameter) (s : Finset (Option ℤ)) :
    Finset LatentQuotient :=
  s.image (fun i => heisenbergFiniteModeLatentReadout (q, i))

/-- Stage inclusion `s ⊆ t` preserves `heisenbergFiniteModeStageLatentImage q`. -/
theorem heisenbergFiniteModeStageLatentImage_mono
    (q : SixthRootParameter) {s t : Finset (Option ℤ)} (hst : s ⊆ t) :
    heisenbergFiniteModeStageLatentImage q s ⊆
      heisenbergFiniteModeStageLatentImage q t := by
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨i, hi, rfl⟩
  exact Finset.mem_image.mpr ⟨i, hst hi, Eq.refl _⟩

/-- Every basis index `i ∈ s` contributes its cyclotomic degree to the first Weyl residue
projection of `heisenbergFiniteModeStageLatentImage q s`. -/
theorem heisenbergFiniteModeStageLatentImage_degree_mem
    (q : SixthRootParameter) (s : Finset (Option ℤ))
    (i : Option ℤ) (hi : i ∈ s) :
    (heisenbergFiniteModeLatentReadout (q, i)).2.1 ∈
      (heisenbergFiniteModeStageLatentImage q s).image (fun z => z.2.1) := by
  unfold heisenbergFiniteModeStageLatentImage
  exact Finset.mem_image.mpr ⟨heisenbergFiniteModeLatentReadout (q, i),
    Finset.mem_image.mpr ⟨i, hi, Eq.refl _⟩, Eq.refl _⟩

end
end InfoGeometry.Topology.HeisenbergFiniteModeLatentReadoutTopological
