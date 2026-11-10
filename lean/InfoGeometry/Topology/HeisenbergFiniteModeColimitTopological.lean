/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.HeisenbergFiniteModeColimit

/-!
# Topological Readout for the Finite-Mode Heisenberg Colimit

This module equips `heisenbergFiniteModeColimit` and `HeisenbergAlgebra 𝕜` with
discrete topologies, defines `topologicalHeisenbergFiniteModeColimitMap`, and
proves its evaluation, continuity, surjectivity, injectivity, and local constancy.

- BUCKET 1 (Established Mathematical Target & Existing Owners):
  * `InfoGeometry.Canonical.HeisenbergFiniteModeColimit`:
    `heisenbergFiniteModeColimit`, `heisenbergFiniteModeColimitMap`,
    `heisenbergFiniteModeColimitMap_surjective`,
    `heisenbergFiniteModeColimitMap_injective`.
- BUCKET 2 (Deconfabulation):
  * All algebraic and topological properties are proved via explicit unfolding and
    reduction to the canonical colimit theorems.
- BUCKET 3 (Constructive Lean 4 Theorems Proved Here):
  * `topologicalHeisenbergFiniteModeColimitMap`.
  * `topologicalHeisenbergFiniteModeColimitMap_eq`.
  * `continuous_topologicalHeisenbergFiniteModeColimitMap`,
    `surjective_topologicalHeisenbergFiniteModeColimitMap`,
    `injective_topologicalHeisenbergFiniteModeColimitMap`,
    `isLocallyConstant_topologicalHeisenbergFiniteModeColimitMap`.
-/

namespace InfoGeometry.Topology.HeisenbergFiniteModeColimitTopological

open InfoGeometry.Canonical
open VirasoroProject

noncomputable section

variable {𝕜 : Type*} [Field 𝕜]

instance heisenbergFiniteModeColimitTopologicalSpace :
    TopologicalSpace (heisenbergFiniteModeColimit (𝕜 := 𝕜)) := ⊥

instance heisenbergFiniteModeColimitDiscreteTopology :
    DiscreteTopology (heisenbergFiniteModeColimit (𝕜 := 𝕜)) := DiscreteTopology.mk (Eq.refl _)

instance heisenbergAlgebraTopologicalSpace :
    TopologicalSpace (HeisenbergAlgebra 𝕜) := ⊥

instance heisenbergAlgebraDiscreteTopology :
    DiscreteTopology (HeisenbergAlgebra 𝕜) := DiscreteTopology.mk (Eq.refl _)

/-- The finite-mode Heisenberg colimit map viewed as a topological readout. -/
def topologicalHeisenbergFiniteModeColimitMap :
    heisenbergFiniteModeColimit (𝕜 := 𝕜) → HeisenbergAlgebra 𝕜 :=
  fun x => (heisenbergFiniteModeColimitMap (𝕜 := 𝕜)).hom x

/-- Explicit identification of `topologicalHeisenbergFiniteModeColimitMap` with the
underlying linear map of `heisenbergFiniteModeColimitMap`. -/
@[simp] theorem topologicalHeisenbergFiniteModeColimitMap_eq :
    topologicalHeisenbergFiniteModeColimitMap (𝕜 := 𝕜) =
      (heisenbergFiniteModeColimitMap (𝕜 := 𝕜)).hom := by
  unfold topologicalHeisenbergFiniteModeColimitMap
  exact Eq.refl _

/-- The finite-mode Heisenberg colimit map is continuous for the discrete topology. -/
theorem continuous_topologicalHeisenbergFiniteModeColimitMap :
    Continuous (topologicalHeisenbergFiniteModeColimitMap (𝕜 := 𝕜)) := by
  unfold topologicalHeisenbergFiniteModeColimitMap
  exact continuous_of_discreteTopology

/-- The topological readout is surjective onto `HeisenbergAlgebra 𝕜`. -/
theorem surjective_topologicalHeisenbergFiniteModeColimitMap :
    Function.Surjective
      (topologicalHeisenbergFiniteModeColimitMap (𝕜 := 𝕜)) := by
  rw [topologicalHeisenbergFiniteModeColimitMap_eq]
  exact heisenbergFiniteModeColimitMap_surjective (𝕜 := 𝕜)

/-- The topological readout is injective on `heisenbergFiniteModeColimit`. -/
theorem injective_topologicalHeisenbergFiniteModeColimitMap :
    Function.Injective
      (topologicalHeisenbergFiniteModeColimitMap (𝕜 := 𝕜)) := by
  rw [topologicalHeisenbergFiniteModeColimitMap_eq]
  exact heisenbergFiniteModeColimitMap_injective (𝕜 := 𝕜)

/-- The finite-mode Heisenberg colimit map is locally constant for the discrete topology. -/
theorem isLocallyConstant_topologicalHeisenbergFiniteModeColimitMap :
    IsLocallyConstant (topologicalHeisenbergFiniteModeColimitMap (𝕜 := 𝕜)) := by
  unfold topologicalHeisenbergFiniteModeColimitMap
  exact IsLocallyConstant.of_discrete

end
end InfoGeometry.Topology.HeisenbergFiniteModeColimitTopological
