/-
Copyright (c) 2026 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import Mathlib.Algebra.Lie.Loop
import InfoGeometry.External.Virasoro.CentralExtension
import InfoGeometry.External.Virasoro.LieCohomologySmallDegree

/-!
# Affine Kac-Moody algebra

This file defines the untwisted affine Kac-Moody algebra as a central extension of the
loop algebra `loopAlgebra 𝕜 ℤ 𝓰`.

## Main definitions

* `VirasoroProject.affineKacMoodyCocycle`: The 2-cocycle defining the central extension,
  transported from Mathlib's `LieAlgebra.LoopAlgebra.twoCocycleOfBilinear`.
* `VirasoroProject.AffineKacMoody`: The affine Kac-Moody algebra.
-/

namespace VirasoroProject

open LieAlgebra
open LieAlgebra.LoopAlgebra

universe u
variable (𝕜 : Type u) [CommRing 𝕜] [IsAddTorsionFree 𝕜]
variable (𝓰 : Type u) [LieRing 𝓰] [LieAlgebra 𝕜 𝓰]
variable (Φ : LinearMap.BilinForm 𝕜 𝓰)
variable (hΦ : Φ.lieInvariant 𝓰) (hΦs : Φ.IsSymm)

/-- Mathlib's `Cohomology.twoCochain` corresponds to `LieTwoCocycle.toBilin` + `self'`. -/
noncomputable def affineKacMoodyCocycle : LieTwoCocycle 𝕜 (loopAlgebra 𝕜 ℤ 𝓰) 𝕜 where
  toBilin := residuePairing 𝕜 ℤ 𝓰 Φ
  self' := by
    let c := twoCochainOfBilinear 𝕜 ℤ 𝓰 Φ hΦs
    intro X
    have h : c X X = 0 := LieModule.Cohomology.twoCochain_alt c X
    have h_def :
        c X X =
          (TrivialLieModule.equiv 𝕜 (loopAlgebra 𝕜 ℤ 𝓰) 𝕜).symm (residuePairing 𝕜 ℤ 𝓰 Φ X X) :=
      rfl
    rw [h_def] at h
    have h2 := congrArg (TrivialLieModule.equiv 𝕜 (loopAlgebra 𝕜 ℤ 𝓰) 𝕜) h
    simpa using h2
  leibniz' := by
    let c := twoCocycleOfBilinear 𝕜 ℤ 𝓰 Φ hΦ hΦs
    intro X Y Z
    have h_cocycle := (LieModule.Cohomology.mem_twoCocycle_iff_of_trivial (a := c.val)).mp c.property
    have h_eq := h_cocycle X Y Z
    have h_def (U V) :
        c.val U V =
          (TrivialLieModule.equiv 𝕜 (loopAlgebra 𝕜 ℤ 𝓰) 𝕜).symm (residuePairing 𝕜 ℤ 𝓰 Φ U V) :=
      rfl
    simp only [h_def] at h_eq
    have h2 := congrArg (TrivialLieModule.equiv 𝕜 (loopAlgebra 𝕜 ℤ 𝓰) 𝕜) h_eq
    simpa using h2

/-- The untwisted affine Kac-Moody algebra. -/
abbrev AffineKacMoody :=
  LieTwoCocycle.CentralExtension (affineKacMoodyCocycle 𝕜 𝓰 Φ hΦ hΦs)

end VirasoroProject
