/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.PeirceCompressionCStar
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Tactic.GCongr

/-!
# Localization through an isometric Hilbert-space embedding

For an actual isometry `V : E →ₗᵢ[𝕜] F`, localization `V† S V` on `E`
and compression `P S P` on `F`, where `P = V V†`, have the same operator
norm. The range projection is identified with the native orthogonal projection
onto the actual range of `V`.

For a projection symbol, the failure of localization to be a projection is
exactly the Gram operator of the rectangular leakage map `(1-P) Q V`.
The algebraic factorization is transported from the existing Peirce owner.
No finite dimension, surjectivity of `V`, or commutation of `P` and `Q` is
assumed. No Gaussian transform or geometric porosity estimate is constructed.
-/

noncomputable section

namespace InfoGeometry.Analysis.HilbertLocalization

open ContinuousLinearMap
open scoped InnerProductSpace

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- The actual ambient range projection of the isometric embedding. -/
def rangeProjection (V : E →ₗᵢ[𝕜] F) : F →L[𝕜] F :=
  V.toContinuousLinearMap ∘L V.toContinuousLinearMap.adjoint

/-- Embed a source operator into the ambient range corner. -/
def embed (V : E →ₗᵢ[𝕜] F) (T : E →L[𝕜] E) : F →L[𝕜] F :=
  V.toContinuousLinearMap ∘L T ∘L V.toContinuousLinearMap.adjoint

/-- Pull an ambient symbol back to the source Hilbert space. -/
def localization (V : E →ₗᵢ[𝕜] F) (S : F →L[𝕜] F) : E →L[𝕜] E :=
  V.toContinuousLinearMap.adjoint ∘L S ∘L V.toContinuousLinearMap

/-- Compress a bounded ambient symbol to the range corner. -/
def toeplitz (V : E →ₗᵢ[𝕜] F) (S : F →L[𝕜] F) : F →L[𝕜] F :=
  rangeProjection V * S * rangeProjection V

@[simp]
theorem adjoint_apply_isometry (V : E →ₗᵢ[𝕜] F) (x : E) :
    V.toContinuousLinearMap.adjoint (V x) = x := by
  exact congrArg (fun T : E →L[𝕜] E => T x) V.adjoint_comp_self

@[simp]
theorem rangeProjection_apply_isometry (V : E →ₗᵢ[𝕜] F) (x : E) :
    rangeProjection V (V x) = V x := by
  simp [rangeProjection]

theorem isStarProjection_rangeProjection (V : E →ₗᵢ[𝕜] F) :
    IsStarProjection (rangeProjection V) := by
  constructor
  · ext x
    simp [rangeProjection]
  · change (rangeProjection V).adjoint = rangeProjection V
    simp [rangeProjection, adjoint_comp]

theorem range_rangeProjection (V : E →ₗᵢ[𝕜] F) :
    (rangeProjection V).range = V.toLinearMap.range := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨V.toContinuousLinearMap.adjoint x, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨V x, rangeProjection_apply_isometry V x⟩

local instance rangeCompleteSpace (V : E →ₗᵢ[𝕜] F) :
    CompleteSpace V.toLinearMap.range :=
  V.equivRange.toIsometryEquiv.symm.completeSpace

/-- Identification with Mathlib's orthogonal projection onto the actual range. -/
theorem rangeProjection_eq_starProjection (V : E →ₗᵢ[𝕜] F) :
    rangeProjection V = V.toLinearMap.range.starProjection := by
  apply (isStarProjection_rangeProjection V).ext (isStarProjection_starProjection)
  rw [range_rangeProjection, Submodule.range_starProjection]

@[simp]
theorem embed_one (V : E →ₗᵢ[𝕜] F) : embed V 1 = rangeProjection V := by
  simp [embed, rangeProjection, one_def]

@[simp]
theorem embed_sub (V : E →ₗᵢ[𝕜] F) (S T : E →L[𝕜] E) :
    embed V (S - T) = embed V S - embed V T := by
  ext x
  simp [embed]

theorem embed_mul (V : E →ₗᵢ[𝕜] F) (S T : E →L[𝕜] E) :
    embed V (S * T) = embed V S * embed V T := by
  ext x
  simp [embed]

theorem adjoint_embed (V : E →ₗᵢ[𝕜] F) (T : E →L[𝕜] E) :
    (embed V T).adjoint = embed V T.adjoint := by
  simp [embed, adjoint_comp, comp_assoc]

@[simp]
theorem localization_embed (V : E →ₗᵢ[𝕜] F) (T : E →L[𝕜] E) :
    localization V (embed V T) = T := by
  ext x
  simp [localization, embed]

theorem embed_injective (V : E →ₗᵢ[𝕜] F) : Function.Injective (embed V) := by
  intro S T h
  simpa using congrArg (localization V) h

theorem embed_localization (V : E →ₗᵢ[𝕜] F) (S : F →L[𝕜] F) :
    embed V (localization V S) = toeplitz V S := by
  simp [embed, localization, toeplitz, rangeProjection, mul_def, comp_assoc]

theorem isometry_comp_localization (V : E →ₗᵢ[𝕜] F) (S : F →L[𝕜] F) :
    V.toContinuousLinearMap ∘L localization V S =
      toeplitz V S ∘L V.toContinuousLinearMap := by
  ext x
  simp [localization, toeplitz, rangeProjection]

@[simp]
theorem localization_toeplitz (V : E →ₗᵢ[𝕜] F) (S : F →L[𝕜] F) :
    localization V (toeplitz V S) = localization V S := by
  rw [← embed_localization, localization_embed]

/-- Right composition by the adjoint of an isometry preserves the operator norm. -/
theorem norm_comp_adjoint_isometry {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
    (V : E →ₗᵢ[𝕜] F) (A : E →L[𝕜] G) :
    ‖A ∘L V.toContinuousLinearMap.adjoint‖ = ‖A‖ := by
  calc
    _ = ‖(A ∘L V.toContinuousLinearMap.adjoint).adjoint‖ :=
      (adjoint.norm_map _).symm
    _ = ‖V.toContinuousLinearMap ∘L A.adjoint‖ := by
      rw [adjoint_comp, adjoint_adjoint]
    _ = ‖A.adjoint‖ := V.norm_toContinuousLinearMap_comp
    _ = ‖A‖ := adjoint.norm_map A

@[simp]
theorem norm_embed (V : E →ₗᵢ[𝕜] F) (T : E →L[𝕜] E) :
    ‖embed V T‖ = ‖T‖ := by
  rw [embed, V.norm_toContinuousLinearMap_comp, norm_comp_adjoint_isometry]

/-- Localization and ambient range compression have exactly the same norm. -/
theorem norm_localization_eq_toeplitz (V : E →ₗᵢ[𝕜] F) (S : F →L[𝕜] F) :
    ‖localization V S‖ = ‖toeplitz V S‖ := by
  rw [← embed_localization, norm_embed]

/-- Positive powers respect the nonunital ambient embedding. -/
theorem embed_pow_succ (V : E →ₗᵢ[𝕜] F) (T : E →L[𝕜] E) (n : ℕ) :
    embed V (T ^ (n + 1)) = embed V T ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, embed_mul, ih, ← pow_succ]

/-- Pullback of ambient powers includes exponent zero, even for a proper isometry. -/
theorem localization_pow_toeplitz (V : E →ₗᵢ[𝕜] F) (S : F →L[𝕜] F) (n : ℕ) :
    localization V (toeplitz V S ^ n) = localization V S ^ n := by
  cases n with
  | zero => simp [localization, one_def]
  | succ n =>
    rw [← embed_localization, ← embed_pow_succ, localization_embed]

theorem norm_localization_pow_succ (V : E →ₗᵢ[𝕜] F) (S : F →L[𝕜] F) (n : ℕ) :
    ‖localization V S ^ (n + 1)‖ = ‖toeplitz V S ^ (n + 1)‖ := by
  rw [← embed_localization, ← embed_pow_succ, norm_embed]

theorem norm_localization_le (V : E →ₗᵢ[𝕜] F) (S : F →L[𝕜] F) :
    ‖localization V S‖ ≤ ‖S‖ := by
  rw [norm_localization_eq_toeplitz, toeplitz]
  have hp : ‖rangeProjection V‖ ≤ 1 :=
    IsStarProjection.norm_le _ (isStarProjection_rangeProjection V)
  calc
    _ ≤ ‖rangeProjection V‖ * ‖S‖ * ‖rangeProjection V‖ :=
      (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ 1 * ‖S‖ * 1 := by gcongr
    _ = ‖S‖ := by simp

theorem isPositive_localization (V : E →ₗᵢ[𝕜] F) (S : F →L[𝕜] F)
    (hS : S.IsPositive) : (localization V S).IsPositive :=
  hS.adjoint_conj V.toContinuousLinearMap

@[simp]
theorem localization_one_sub (V : E →ₗᵢ[𝕜] F) (S : F →L[𝕜] F) :
    localization V (1 - S) = 1 - localization V S := by
  ext x
  simp [localization]

theorem projection_localization_positive (V : E →ₗᵢ[𝕜] F) (Q : F →L[𝕜] F)
    (hQ : IsStarProjection Q) : (localization V Q).IsPositive :=
  isPositive_localization V Q (.of_isStarProjection hQ)

theorem complement_localization_positive (V : E →ₗᵢ[𝕜] F) (Q : F →L[𝕜] F)
    (hQ : IsStarProjection Q) : (1 - localization V Q).IsPositive := by
  rw [← localization_one_sub]
  exact projection_localization_positive V (1 - Q) hQ.one_sub

theorem projection_localization_selfAdjoint (V : E →ₗᵢ[𝕜] F) (Q : F →L[𝕜] F)
    (hQ : IsStarProjection Q) : IsSelfAdjoint (localization V Q) :=
  (projection_localization_positive V Q hQ).isSelfAdjoint

theorem norm_projection_localization_le_one (V : E →ₗᵢ[𝕜] F) (Q : F →L[𝕜] F)
    (hQ : IsStarProjection Q) : ‖localization V Q‖ ≤ 1 :=
  (norm_localization_le V Q).trans (IsStarProjection.norm_le Q hQ)

/-- Transfer from the embedded source through the symbol to the complementary range. -/
def leakage (V : E →ₗᵢ[𝕜] F) (Q : F →L[𝕜] F) : E →L[𝕜] F :=
  (1 - rangeProjection V) ∘L Q ∘L V.toContinuousLinearMap

theorem leakage_comp_adjoint (V : E →ₗᵢ[𝕜] F) (Q : F →L[𝕜] F) :
    leakage V Q ∘L V.toContinuousLinearMap.adjoint =
      (1 - rangeProjection V) * Q * rangeProjection V := by
  simp [leakage, rangeProjection, mul_def, comp_assoc]

/-- The rectangular Gram operator measures the exact failure of idempotency. -/
theorem localization_defect_eq_leakage_gram
    (V : E →ₗᵢ[𝕜] F) (Q : F →L[𝕜] F) (hQ : IsStarProjection Q) :
    localization V Q - localization V Q * localization V Q =
      (leakage V Q).adjoint ∘L leakage V Q := by
  have hp := isStarProjection_rangeProjection V
  have h := InfoGeometry.Core.PeirceCompressionDefect.compression_adjoint_mul_defect
    (rangeProjection V) Q Q hp.isIdempotentElem.eq hp.isSelfAdjoint.star_eq
  simp only [hQ.isSelfAdjoint.star_eq, hQ.isIdempotentElem.eq] at h
  apply embed_injective V
  calc
    _ = toeplitz V Q - toeplitz V Q * toeplitz V Q := by
      rw [embed_sub, embed_mul, embed_localization]
    _ = star ((1 - rangeProjection V) * Q * rangeProjection V) *
          ((1 - rangeProjection V) * Q * rangeProjection V) := h
    _ = embed V ((leakage V Q).adjoint ∘L leakage V Q) := by
      simp only [← leakage_comp_adjoint]
      simp [embed, star_eq_adjoint, mul_def, adjoint_comp, comp_assoc]

theorem localization_defect_isPositive
    (V : E →ₗᵢ[𝕜] F) (Q : F →L[𝕜] F) (hQ : IsStarProjection Q) :
    (localization V Q - localization V Q * localization V Q).IsPositive := by
  rw [localization_defect_eq_leakage_gram V Q hQ]
  exact isPositive_adjoint_comp_self _

theorem localization_defect_quadratic_form
    (V : E →ₗᵢ[𝕜] F) (Q : F →L[𝕜] F) (hQ : IsStarProjection Q) (x : E) :
    RCLike.re ⟪(localization V Q - localization V Q * localization V Q) x, x⟫_𝕜 =
      ‖leakage V Q x‖ ^ 2 := by
  rw [localization_defect_eq_leakage_gram V Q hQ]
  exact ((leakage V Q).apply_norm_sq_eq_inner_adjoint_left x).symm

theorem norm_localization_defect
    (V : E →ₗᵢ[𝕜] F) (Q : F →L[𝕜] F) (hQ : IsStarProjection Q) :
    ‖localization V Q - localization V Q * localization V Q‖ = ‖leakage V Q‖ ^ 2 := by
  rw [localization_defect_eq_leakage_gram V Q hQ, norm_adjoint_comp_self, pow_two]

theorem localization_idempotent_iff_leakage_zero
    (V : E →ₗᵢ[𝕜] F) (Q : F →L[𝕜] F) (hQ : IsStarProjection Q) :
    IsIdempotentElem (localization V Q) ↔ leakage V Q = 0 := by
  rw [IsIdempotentElem, eq_comm, ← sub_eq_zero, localization_defect_eq_leakage_gram V Q hQ,
    adjoint_comp_self_eq_zero_iff]

/-- Localization preserves projection idempotency exactly when the symbol
commutes with the actual range projection. -/
theorem localization_idempotent_iff_commute
    (V : E →ₗᵢ[𝕜] F) (Q : F →L[𝕜] F) (hQ : IsStarProjection Q) :
    IsIdempotentElem (localization V Q) ↔
      rangeProjection V * Q = Q * rangeProjection V := by
  have hp := isStarProjection_rangeProjection V
  have h := InfoGeometry.Core.PeirceCompressionCStar.compression_square_eq_iff
    (rangeProjection V) Q hp.isIdempotentElem.eq hp.isSelfAdjoint.star_eq
    hQ.isSelfAdjoint.star_eq
  rw [hQ.isIdempotentElem.eq] at h
  change toeplitz V Q = toeplitz V Q * toeplitz V Q ↔ _ at h
  rw [← h]
  change localization V Q * localization V Q = localization V Q ↔ _
  rw [← (embed_injective V).eq_iff, embed_mul, embed_localization]
  exact eq_comm

end InfoGeometry.Analysis.HilbertLocalization
