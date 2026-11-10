/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.HeisenbergFiniteModeLatentReadoutTopological

/-!
# Clopen Stage Exhaustion of Heisenberg Latent Labels

This module defines the finite-stage subset `heisenbergFiniteModeStageLatentSet q s`
of `LatentQuotient`, proves that each stage set is clopen and monotone under stage
inclusion, and proves that the indexed union over all finite stages `s : Finset (Option ℤ)`
equals the full range `Set.range (fun i => heisenbergFiniteModeLatentReadout (q, i))`.

- BUCKET 1 (Established Mathematical Target & Existing Owners):
  * `InfoGeometry.Topology.HeisenbergFiniteModeLatentReadoutTopological`:
    `heisenbergFiniteModeLatentReadout`, `heisenbergFiniteModeStageLatentImage`,
    `heisenbergFiniteModeStageLatentImage_mono`.
- BUCKET 2 (Deconfabulation):
  * Clopenness, stage monotonicity, and indexed union exhaustion are proved
    constructively.
- BUCKET 3 (Constructive Lean 4 Theorems Proved Here):
  * `heisenbergFiniteModeStageLatentSet`.
  * `isClopen_heisenbergFiniteModeStageLatentSet`,
    `heisenbergFiniteModeStageLatentSet_mono`,
    `iUnion_heisenbergFiniteModeStageLatentSet`.
-/

namespace InfoGeometry.Topology.HeisenbergFiniteModeLatentStageUnionTopological

open InfoGeometry.Topology.HeisenbergFiniteModeLatentReadoutTopological
open InfoGeometry.Topology.HeisenbergCyclotomicAtlasTopological
open InfoGeometry.Topology.CyclotomicLatentQuotientTopological

noncomputable section

variable {𝕜 : Type*} [Ring 𝕜]

/-- The latent subset of `LatentQuotient` visible at a finite mode stage `s`. -/
def heisenbergFiniteModeStageLatentSet
    (q : SixthRootParameter) (s : Finset (Option ℤ)) :
    Set LatentQuotient :=
  ↑(heisenbergFiniteModeStageLatentImage q s)

/-- Every finite-stage latent set is clopen in the discrete quotient chart. -/
theorem isClopen_heisenbergFiniteModeStageLatentSet
    (q : SixthRootParameter) (s : Finset (Option ℤ)) :
    IsClopen (heisenbergFiniteModeStageLatentSet q s) := by
  unfold heisenbergFiniteModeStageLatentSet
  exact isClopen_discrete _

/-- Stage inclusion `s ⊆ t` preserves `heisenbergFiniteModeStageLatentSet q`. -/
theorem heisenbergFiniteModeStageLatentSet_mono
    (q : SixthRootParameter) {s t : Finset (Option ℤ)} (hst : s ⊆ t) :
    heisenbergFiniteModeStageLatentSet q s ⊆
      heisenbergFiniteModeStageLatentSet q t := by
  intro z hz
  exact heisenbergFiniteModeStageLatentImage_mono q hst hz

/-- The union over all finite stages equals the full range of basis-index latent labels. -/
theorem iUnion_heisenbergFiniteModeStageLatentSet
    (q : SixthRootParameter) :
    (⋃ s : Finset (Option ℤ), heisenbergFiniteModeStageLatentSet q s) =
      Set.range (fun i : Option ℤ =>
        heisenbergFiniteModeLatentReadout (q, i)) := by
  ext z
  constructor
  · intro hz
    rcases Set.mem_iUnion.mp hz with ⟨s, hz⟩
    change z ∈ heisenbergFiniteModeStageLatentImage q s at hz
    rcases Finset.mem_image.mp hz with ⟨i, _hi, hzi⟩
    exact ⟨i, hzi⟩
  · intro hz
    rcases hz with ⟨i, rfl⟩
    refine Set.mem_iUnion.mpr ⟨{i}, ?_⟩
    change heisenbergFiniteModeLatentReadout (q, i) ∈
      heisenbergFiniteModeStageLatentImage q {i}
    exact Finset.mem_image.mpr ⟨i, Finset.mem_singleton_self i, Eq.refl _⟩

end
end InfoGeometry.Topology.HeisenbergFiniteModeLatentStageUnionTopological
