/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.DrazinSpectralBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.DrazinSpectralProjectorBridge

Load-bearing downstream consumer of `DrazinSpectralBridge`.

This file turns the bundled infinite-dimensional spectral package at `0` into
explicit projector-level consequences for the recovered Drazin witness:

- idempotence of the regular projector `P`,
- idempotence of the defect projector `P₀`,
- orthogonality `P * P₀ = 0 = P₀ * P`,
- decomposition `P + P₀ = 1`.
-/

namespace InfoGeometry.Canonical.DrazinSpectralProjectorBridge

open DrazinInfiniteCore
open DrazinSpectralBridge
open InfoGeometry.Canonical.Drazin

variable {𝕂 E : Type*} [NormedField 𝕂] [NormedAddCommGroup E] [NormedSpace 𝕂 E]
variable {T : E →L[𝕂] E}

/--
From finite ascent/descent at `0`, recover a Drazin witness together with the
full regular/defect projector algebra.  Spectral isolation at `0` is not needed
for this implication, so it is not taken as a hypothesis.
-/
@[rep_depth operator]
theorem exists_drazinInverse_with_projector_split_of_finiteAscentDescentAtZero
    (hFinite : HasFiniteAscentDescentAtZero T.toLinearMap) :
    ∃ k TD, IsDrazinInverse T.toLinearMap TD k
      ∧ IsDrazinInverse.projection T.toLinearMap TD * IsDrazinInverse.projection T.toLinearMap TD
          = IsDrazinInverse.projection T.toLinearMap TD
      ∧ IsDrazinInverse.complementaryProjection T.toLinearMap TD
            * IsDrazinInverse.complementaryProjection T.toLinearMap TD
          = IsDrazinInverse.complementaryProjection T.toLinearMap TD
      ∧ IsDrazinInverse.projection T.toLinearMap TD
            * IsDrazinInverse.complementaryProjection T.toLinearMap TD
          = 0
      ∧ IsDrazinInverse.complementaryProjection T.toLinearMap TD
            * IsDrazinInverse.projection T.toLinearMap TD
          = 0
      ∧ IsDrazinInverse.projection T.toLinearMap TD
            + IsDrazinInverse.complementaryProjection T.toLinearMap TD
          = (1 : E →ₗ[𝕂] E) := by
  rcases exists_drazinInverse_of_finiteAscentDescentAtZero (T := T) hFinite with ⟨k, TD, hD⟩
  refine ⟨k, TD, hD, ?_, ?_, ?_, ?_, ?_⟩
  · exact IsDrazinInverse.projection_is_idempotent hD
  · exact IsDrazinInverse.complementaryProjection_is_idempotent hD
  · exact IsDrazinInverse.projection_mul_complementaryProjection hD
  · exact IsDrazinInverse.complementaryProjection_mul_projection hD
  · exact IsDrazinInverse.projection_add_complementaryProjection (a := T.toLinearMap) (b := TD)

/--
From the bundled spectral package, recover a Drazin witness together with the
full regular/defect projector algebra, using the package's finite
ascent/descent field.
-/
@[rep_depth operator]
theorem exists_drazinInverse_with_projector_split_of_drazinInfiniteAssumptions
    (A : DrazinInfiniteAssumptions T) :
    ∃ k TD, IsDrazinInverse T.toLinearMap TD k
      ∧ IsDrazinInverse.projection T.toLinearMap TD * IsDrazinInverse.projection T.toLinearMap TD
          = IsDrazinInverse.projection T.toLinearMap TD
      ∧ IsDrazinInverse.complementaryProjection T.toLinearMap TD
            * IsDrazinInverse.complementaryProjection T.toLinearMap TD
          = IsDrazinInverse.complementaryProjection T.toLinearMap TD
      ∧ IsDrazinInverse.projection T.toLinearMap TD
            * IsDrazinInverse.complementaryProjection T.toLinearMap TD
          = 0
      ∧ IsDrazinInverse.complementaryProjection T.toLinearMap TD
            * IsDrazinInverse.projection T.toLinearMap TD
          = 0
      ∧ IsDrazinInverse.projection T.toLinearMap TD
            + IsDrazinInverse.complementaryProjection T.toLinearMap TD
          = (1 : E →ₗ[𝕂] E) :=
  exists_drazinInverse_with_projector_split_of_finiteAscentDescentAtZero A.finite_ascent_descent

/--
Projection-only corollary of the spectral package:
recover idempotence of the regular projector on the chosen Drazin witness.
-/
@[rep_depth operator]
theorem exists_drazin_projection_idempotent_of_drazinInfiniteAssumptions
    (A : DrazinInfiniteAssumptions T) :
    ∃ k TD, IsDrazinInverse T.toLinearMap TD k
      ∧ IsDrazinInverse.projection T.toLinearMap TD * IsDrazinInverse.projection T.toLinearMap TD
          = IsDrazinInverse.projection T.toLinearMap TD := by
  rcases exists_drazinInverse_with_projector_split_of_drazinInfiniteAssumptions A with
    ⟨k, TD, hD, hPidem, -⟩
  exact ⟨k, TD, hD, hPidem⟩

end InfoGeometry.Canonical.DrazinSpectralProjectorBridge
