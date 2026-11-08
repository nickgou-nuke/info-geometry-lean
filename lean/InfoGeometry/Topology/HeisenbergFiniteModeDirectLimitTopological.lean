/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.HeisenbergFiniteModeDirectLimitBridge

/-!
# Topological Readout for the Heisenberg Finite-Mode Direct-Limit Bridge

This module equips `heisenbergFiniteModeDirectLimit` and `HeisenbergAlgebra 𝕜` with
discrete topologies, defines the underlying map `topologicalHeisenbergFiniteModeDirectLimitMap`,
and proves its evaluation, continuity, surjectivity, injectivity, and local constancy.

- BUCKET 1 (Established Mathematical Target & Existing Owners):
  * `InfoGeometry.Canonical.HeisenbergFiniteModeDirectLimitBridge`:
    `heisenbergFiniteModeDirectLimit`, `heisenbergFiniteModeDirectLimitMap`,
    `heisenbergFiniteModeDirectLimitMap_surjective`,
    `heisenbergFiniteModeDirectLimitMap_injective`.
- BUCKET 2 (Deconfabulation):
  * All algebraic and topological properties are proved via explicit unfolding and
    reduction to the canonical direct-limit bridge theorems.
- BUCKET 3 (Constructive Lean 4 Theorems Proved Here):
  * `topologicalHeisenbergFiniteModeDirectLimitMap`.
  * `topologicalHeisenbergFiniteModeDirectLimitMap_eq`.
  * `continuous_topologicalHeisenbergFiniteModeDirectLimitMap`,
    `surjective_topologicalHeisenbergFiniteModeDirectLimitMap`,
    `injective_topologicalHeisenbergFiniteModeDirectLimitMap`,
    `isLocallyConstant_topologicalHeisenbergFiniteModeDirectLimitMap`.
-/

namespace InfoGeometry.Topology.HeisenbergFiniteModeDirectLimitTopological

open InfoGeometry.Canonical.HeisenbergFiniteModeDirectLimitBridge
open VirasoroProject

noncomputable section

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]

instance heisenbergFiniteModeDirectLimitTopologicalSpace :
    TopologicalSpace (heisenbergFiniteModeDirectLimit (𝕜 := 𝕜)) := ⊥

instance heisenbergFiniteModeDirectLimitDiscreteTopology :
    DiscreteTopology (heisenbergFiniteModeDirectLimit (𝕜 := 𝕜)) := DiscreteTopology.mk (Eq.refl _)

instance heisenbergFiniteModeDirectLimitTargetTopologicalSpace :
    TopologicalSpace (HeisenbergAlgebra 𝕜) := ⊥

instance heisenbergFiniteModeDirectLimitTargetDiscreteTopology :
    DiscreteTopology (HeisenbergAlgebra 𝕜) := DiscreteTopology.mk (Eq.refl _)

/-- The Heisenberg finite-mode direct-limit map viewed as a topological readout. -/
def topologicalHeisenbergFiniteModeDirectLimitMap :
    heisenbergFiniteModeDirectLimit (𝕜 := 𝕜) → HeisenbergAlgebra 𝕜 :=
  fun x => (heisenbergFiniteModeDirectLimitMap (𝕜 := 𝕜)).hom x

/-- Explicit identification of `topologicalHeisenbergFiniteModeDirectLimitMap` with the
underlying linear map of `heisenbergFiniteModeDirectLimitMap`. -/
@[simp] theorem topologicalHeisenbergFiniteModeDirectLimitMap_eq :
    topologicalHeisenbergFiniteModeDirectLimitMap (𝕜 := 𝕜) =
      (heisenbergFiniteModeDirectLimitMap (𝕜 := 𝕜)).hom := by
  unfold topologicalHeisenbergFiniteModeDirectLimitMap
  exact Eq.refl _

/-- The finite-mode direct-limit Heisenberg map is continuous for the discrete topology. -/
theorem continuous_topologicalHeisenbergFiniteModeDirectLimitMap :
    Continuous (topologicalHeisenbergFiniteModeDirectLimitMap (𝕜 := 𝕜)) := by
  unfold topologicalHeisenbergFiniteModeDirectLimitMap
  exact continuous_of_discreteTopology

/-- The direct-limit readout is surjective onto `HeisenbergAlgebra 𝕜`. -/
theorem surjective_topologicalHeisenbergFiniteModeDirectLimitMap :
    Function.Surjective
      (topologicalHeisenbergFiniteModeDirectLimitMap (𝕜 := 𝕜)) := by
  rw [topologicalHeisenbergFiniteModeDirectLimitMap_eq]
  exact heisenbergFiniteModeDirectLimitMap_surjective (𝕜 := 𝕜)

/-- The direct-limit readout is injective on `heisenbergFiniteModeDirectLimit`. -/
theorem injective_topologicalHeisenbergFiniteModeDirectLimitMap :
    Function.Injective
      (topologicalHeisenbergFiniteModeDirectLimitMap (𝕜 := 𝕜)) := by
  rw [topologicalHeisenbergFiniteModeDirectLimitMap_eq]
  exact heisenbergFiniteModeDirectLimitMap_injective (𝕜 := 𝕜)

/-- The direct-limit readout is locally constant for the discrete topology. -/
theorem isLocallyConstant_topologicalHeisenbergFiniteModeDirectLimitMap :
    IsLocallyConstant (topologicalHeisenbergFiniteModeDirectLimitMap (𝕜 := 𝕜)) := by
  unfold topologicalHeisenbergFiniteModeDirectLimitMap
  exact IsLocallyConstant.of_discrete

end
end InfoGeometry.Topology.HeisenbergFiniteModeDirectLimitTopological
