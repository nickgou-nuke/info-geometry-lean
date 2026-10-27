/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Isometric covariance of projection incidence and geometric rank

The conjugation operation is Mathlib's `LinearIsometryEquiv.conjStarAlgEquiv`.
It acts on the full algebra of bounded operators. No commutation hypothesis is
imposed. Geometric rank is the dimension of the sum of ranges, not the dimension
of the span of the projection operators as vectors in their operator algebra.
-/

noncomputable section

namespace InfoGeometry.Projective.ProjectionIncidence

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Orthogonal projection onto an isometric image is operator conjugation. -/
theorem starProjection_map_eq_conj (e : E ≃ₗᵢ[𝕜] F)
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    (U.map e.toLinearEquiv.toLinearMap).starProjection =
      e.conjStarAlgEquiv U.starProjection := by
  ext x
  exact Submodule.starProjection_map_apply e U x

/-- The range of an arbitrary conjugated operator is the image of its range. -/
theorem range_conj (e : E ≃ₗᵢ[𝕜] F) (T : E →L[𝕜] E) :
    (e.conjStarAlgEquiv T).range = T.range.map e.toLinearEquiv.toLinearMap := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨T (e.symm x), ⟨e.symm x, rfl⟩, rfl⟩
  · rintro ⟨x, ⟨z, rfl⟩, rfl⟩
    refine ⟨e z, ?_⟩
    simp only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
      LinearIsometryEquiv.symm_apply_apply]

/-- Range incidence is preserved and reflected by operator conjugation. -/
theorem range_le_range_conj_iff (e : E ≃ₗᵢ[𝕜] F) (S T : E →L[𝕜] E) :
    (e.conjStarAlgEquiv S).range ≤ (e.conjStarAlgEquiv T).range ↔
      S.range ≤ T.range := by
  rw [range_conj, range_conj]
  exact Submodule.map_le_map_iff_of_injective e.injective _ _

/-- Projection absorption is invariant under an arbitrary isometric change of basis. -/
theorem mapped_projection_mul_eq_iff (e : E ≃ₗᵢ[𝕜] F)
    (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    (U.map e.toLinearEquiv.toLinearMap).starProjection *
        (V.map e.toLinearEquiv.toLinearMap).starProjection =
        (U.map e.toLinearEquiv.toLinearMap).starProjection ↔
      U.starProjection * V.starProjection = U.starProjection := by
  rw [starProjection_map_eq_conj, starProjection_map_eq_conj, ← map_mul]
  exact e.conjStarAlgEquiv.injective.eq_iff

/-- The full projection commutator transforms by the native star-algebra equivalence. -/
theorem mapped_projection_commutator (e : E ≃ₗᵢ[𝕜] F)
    (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    (U.map e.toLinearEquiv.toLinearMap).starProjection *
        (V.map e.toLinearEquiv.toLinearMap).starProjection -
      (V.map e.toLinearEquiv.toLinearMap).starProjection *
        (U.map e.toLinearEquiv.toLinearMap).starProjection =
      e.conjStarAlgEquiv
        (U.starProjection * V.starProjection - V.starProjection * U.starProjection) := by
  rw [starProjection_map_eq_conj, starProjection_map_eq_conj]
  simp only [map_sub, map_mul]

/-- Changing orthonormal coordinates cannot turn a noncommuting pair into a commuting pair. -/
theorem mapped_projections_commute_iff (e : E ≃ₗᵢ[𝕜] F)
    (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    Commute (U.map e.toLinearEquiv.toLinearMap).starProjection
        (V.map e.toLinearEquiv.toLinearMap).starProjection ↔
      Commute U.starProjection V.starProjection := by
  rw [starProjection_map_eq_conj, starProjection_map_eq_conj]
  simp only [commute_iff_eq, ← map_mul, e.conjStarAlgEquiv.injective.eq_iff]

section FiniteDimensional

variable [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]

/-- Operator rank is preserved by isometric conjugation. -/
theorem finrank_range_conj (e : E ≃ₗᵢ[𝕜] F) (T : E →L[𝕜] E) :
    Module.finrank 𝕜 (e.conjStarAlgEquiv T).range =
      Module.finrank 𝕜 T.range := by
  rw [range_conj]
  exact e.toLinearEquiv.finrank_map_eq T.range

/-- Rank of a family means rank of its joined ranges and is coordinate invariant. -/
theorem finrank_iSup_range_conj {ι : Sort*} (e : E ≃ₗᵢ[𝕜] F)
    (T : ι → E →L[𝕜] E) :
    Module.finrank 𝕜 (⨆ i, (e.conjStarAlgEquiv (T i)).range) =
      Module.finrank 𝕜 (⨆ i, (T i).range) := by
  simp_rw [range_conj]
  rw [← Submodule.map_iSup]
  exact e.toLinearEquiv.finrank_map_eq _

/-- The rank of a projective join is unchanged under unitary transport. -/
theorem finrank_sup_mapped_projection_ranges (e : E ≃ₗᵢ[𝕜] F)
    (U V : Submodule 𝕜 E) :
    Module.finrank 𝕜
      ((U.map e.toLinearEquiv.toLinearMap).starProjection.range ⊔
        (V.map e.toLinearEquiv.toLinearMap).starProjection.range) =
      Module.finrank 𝕜 (U.starProjection.range ⊔ V.starProjection.range) := by
  simp only [Submodule.range_starProjection]
  rw [← Submodule.map_sup]
  exact e.toLinearEquiv.finrank_map_eq _

end FiniteDimensional

end InfoGeometry.Projective.ProjectionIncidence
