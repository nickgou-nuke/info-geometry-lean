/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.CyclotomicHeisenbergSugawaraProductTopological
import InfoGeometry.Topology.CyclotomicLatentReflectionTopological

/-!
# Reflection of the Cyclotomic Heisenberg / Sugawara Product Chart

This module constructs the homeomorphism `cyclotomicHeisenbergSugawaraReflection`
on `CyclotomicHeisenbergSugawaraOutput 𝕜` acting as `cyclotomicLatentReflection`
on the first factor and the identity on the second factor, and proves its
coordinate projections, involutivity, and continuity.

- BUCKET 1 (Established Mathematical Target & Existing Owners):
  * `InfoGeometry.Topology.CyclotomicHeisenbergSugawaraProductTopological`:
    `CyclotomicHeisenbergSugawaraOutput`.
  * `InfoGeometry.Topology.CyclotomicLatentReflectionTopological`:
    `cyclotomicLatentReflection`, `cyclotomicLatentReflection_involutive`.
- BUCKET 2 (Deconfabulation):
  * Homeomorphism inversion, projections, involutivity, and continuity are proved
    constructively.
- BUCKET 3 (Constructive Lean 4 Theorems Proved Here):
  * `cyclotomicHeisenbergSugawaraReflection`.
  * `cyclotomicHeisenbergSugawaraReflection_latent`,
    `cyclotomicHeisenbergSugawaraReflection_sugawara`,
    `cyclotomicHeisenbergSugawaraReflection_involutive`,
    `continuous_cyclotomicHeisenbergSugawaraReflection`.
-/

namespace InfoGeometry.Topology.CyclotomicHeisenbergSugawaraReflectionTopological

open InfoGeometry.Topology.CyclotomicHeisenbergSugawaraProductTopological
open InfoGeometry.Topology.CyclotomicLatentReflectionTopological

noncomputable section

variable {𝕜 : Type*} [Field 𝕜]

/-- Reflection homeomorphism of the combined chart: latent reflection paired with
Sugawara identity. -/
noncomputable def cyclotomicHeisenbergSugawaraReflection :
    CyclotomicHeisenbergSugawaraOutput 𝕜 ≃ₜ
      CyclotomicHeisenbergSugawaraOutput 𝕜 where
  toFun z := (cyclotomicLatentReflection z.1, z.2)
  invFun z := (cyclotomicLatentReflection z.1, z.2)
  left_inv z := by
    apply Prod.ext
    · exact cyclotomicLatentReflection_involutive z.1
    · exact Eq.refl _
  right_inv z := by
    apply Prod.ext
    · exact cyclotomicLatentReflection_involutive z.1
    · exact Eq.refl _
  continuous_toFun := continuous_of_discreteTopology
  continuous_invFun := continuous_of_discreteTopology

/-- First factor projection of `cyclotomicHeisenbergSugawaraReflection z`. -/
@[simp] theorem cyclotomicHeisenbergSugawaraReflection_latent
    (z : CyclotomicHeisenbergSugawaraOutput 𝕜) :
    (cyclotomicHeisenbergSugawaraReflection z).1 =
      cyclotomicLatentReflection z.1 := by
  unfold cyclotomicHeisenbergSugawaraReflection
  exact Eq.refl _

/-- Second factor projection of `cyclotomicHeisenbergSugawaraReflection z`. -/
@[simp] theorem cyclotomicHeisenbergSugawaraReflection_sugawara
    (z : CyclotomicHeisenbergSugawaraOutput 𝕜) :
    (cyclotomicHeisenbergSugawaraReflection z).2 = z.2 := by
  unfold cyclotomicHeisenbergSugawaraReflection
  exact Eq.refl _

/-- Involutivity of `cyclotomicHeisenbergSugawaraReflection`. -/
theorem cyclotomicHeisenbergSugawaraReflection_involutive
    (z : CyclotomicHeisenbergSugawaraOutput 𝕜) :
    cyclotomicHeisenbergSugawaraReflection
        (cyclotomicHeisenbergSugawaraReflection z) = z := by
  apply Prod.ext
  · rw [cyclotomicHeisenbergSugawaraReflection_latent,
      cyclotomicHeisenbergSugawaraReflection_latent]
    exact cyclotomicLatentReflection_involutive z.1
  · rw [cyclotomicHeisenbergSugawaraReflection_sugawara,
      cyclotomicHeisenbergSugawaraReflection_sugawara]

/-- Continuity of `cyclotomicHeisenbergSugawaraReflection`. -/
theorem continuous_cyclotomicHeisenbergSugawaraReflection :
    Continuous (cyclotomicHeisenbergSugawaraReflection (𝕜 := 𝕜)) := by
  unfold cyclotomicHeisenbergSugawaraReflection
  exact continuous_of_discreteTopology

end
end InfoGeometry.Topology.CyclotomicHeisenbergSugawaraReflectionTopological
