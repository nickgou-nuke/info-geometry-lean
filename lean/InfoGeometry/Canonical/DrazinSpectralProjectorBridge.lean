import InfoGeometry.Canonical.DrazinSpectralBridge
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

namespace DrazinSpectralProjectorBridge

open InfoGeometry.Canonical.DrazinInfiniteCore
open InfoGeometry.Canonical.DrazinSpectralBridge
open InfoGeometry.Canonical.Drazin

variable {𝕂 E : Type*} [NormedField 𝕂] [NormedAddCommGroup E] [NormedSpace 𝕂 E]
variable {T : E →L[𝕂] E}

/--
From isolation at `0` plus finite ascent/descent, recover a Drazin witness
together with the full regular/defect projector algebra.
-/
@[rep_depth operator]
theorem exists_drazinInverse_with_projector_split_of_zeroIsolatedInSpectrum_finiteAscentDescent
    (h : ZeroIsolatedInSpectrum T)
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
  rcases exists_drazinInverse_of_zeroIsolatedInSpectrum_finiteAscentDescent
      (T := T) h hFinite with ⟨k, TD, hD⟩
  refine ⟨k, TD, hD, ?_, ?_, ?_, ?_, ?_⟩
  · exact IsDrazinInverse.projection_is_idempotent hD
  · exact IsDrazinInverse.complementaryProjection_is_idempotent hD
  · exact IsDrazinInverse.projection_mul_complementaryProjection hD
  · exact IsDrazinInverse.complementaryProjection_mul_projection hD
  · exact IsDrazinInverse.projection_add_complementaryProjection (a := T.toLinearMap) (b := TD)

/--
From the bundled spectral package at `0`, recover a Drazin witness together
with the full regular/defect projector algebra on the same witness.
-/
@[rep_depth operator]
theorem exists_drazinInverse_with_projector_split_of_zeroIsolatedInSpectrum_package
    (h : ZeroIsolatedInSpectrum T)
    (hFinite : HasFiniteAscentDescentAtZero T.toLinearMap)
    (_hClassical : HasClassicalRieszDecompositionAtZero T)
    (_hGeneralized : HasGeneralizedRieszDecompositionAtZero T) :
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
  exact exists_drazinInverse_with_projector_split_of_zeroIsolatedInSpectrum_finiteAscentDescent
    (T := T) h hFinite

/--
Projection-only corollary of the spectral package:
recover idempotence of the regular projector on the chosen Drazin witness.
-/
@[rep_depth operator]
theorem exists_drazin_projection_idempotent_of_zeroIsolatedInSpectrum_package
    (h : ZeroIsolatedInSpectrum T)
    (hFinite : HasFiniteAscentDescentAtZero T.toLinearMap)
    (_hClassical : HasClassicalRieszDecompositionAtZero T)
    (_hGeneralized : HasGeneralizedRieszDecompositionAtZero T) :
    ∃ k TD, IsDrazinInverse T.toLinearMap TD k
      ∧ IsDrazinInverse.projection T.toLinearMap TD * IsDrazinInverse.projection T.toLinearMap TD
          = IsDrazinInverse.projection T.toLinearMap TD := by
  rcases exists_drazinInverse_with_projector_split_of_zeroIsolatedInSpectrum_finiteAscentDescent
      (T := T) h hFinite with
    ⟨k, TD, hD, hPidem, _hQidem, _hPQ, _hQP, _hDecomp⟩
  exact ⟨k, TD, hD, hPidem⟩

end DrazinSpectralProjectorBridge
