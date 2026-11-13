/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic.Linarith

/-!
# Complementary Hilbert localization energy

The maps act on actual, possibly different Hilbert spaces. Orthogonal
projection gives an exact retained/complementary energy partition. A lower
bound on the complementary energy then gives an operator norm contraction.
That lower bound is an explicit analytic premise, not a consequence of the
partition or an assumption about the number of points in a finite mask.
-/

noncomputable section

open ContinuousLinearMap

namespace InfoGeometry.Analysis.HilbertLocalizationEnergy

variable {𝕜 E F : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Native orthogonal projection Pythagoras, stated for a star projection. -/
theorem projection_energy (Q : F →L[𝕜] F) (hQ : IsStarProjection Q) (y : F) :
    ‖Q y‖ ^ 2 + ‖(1 - Q) y‖ ^ 2 = ‖y‖ ^ 2 := by
  obtain ⟨hRange, hQrange⟩ := isStarProjection_iff_eq_starProjection_range.mp hQ
  let := hRange
  simpa only [Submodule.starProjection_orthogonal', ← hQrange] using
    (Submodule.norm_sq_eq_add_norm_sq_starProjection y Q.range).symm

/-- Retained and complementary energies after an isometric transform add
to the input energy. The prelocalizing operator need not itself be a projection. -/
theorem localization_energy (U : E →ₗᵢ[𝕜] F) (P : E →L[𝕜] E)
    (Q : F →L[𝕜] F) (hQ : IsStarProjection Q) (x : E) :
    ‖Q (U (P x))‖ ^ 2 + ‖(1 - Q) (U (P x))‖ ^ 2 = ‖P x‖ ^ 2 := by
  simpa only [U.norm_map] using projection_energy Q hQ (U (P x))

variable [CompleteSpace E]

/-- A quantified complementary energy loss bounds the actual rectangular
localization operator. Only `δ ≤ 1` is needed for this implication; a positive
`δ` yields strict contraction. -/
theorem localization_norm_le_of_leakage (U : E →ₗᵢ[𝕜] F)
    (P : E →L[𝕜] E) (Q : F →L[𝕜] F)
    (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    {δ : ℝ} (hδ : δ ≤ 1)
    (hLoss : ∀ x, δ * ‖P x‖ ^ 2 ≤ ‖(1 - Q) (U (P x))‖ ^ 2) :
    ‖Q ∘L U.toContinuousLinearMap ∘L P‖ ≤ Real.sqrt (1 - δ) := by
  have hRemaining : 0 ≤ 1 - δ := sub_nonneg.mpr hδ
  refine opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
  have hEnergy := localization_energy U P Q hQ x
  have hRetained : ‖Q (U (P x))‖ ^ 2 ≤ (1 - δ) * ‖P x‖ ^ 2 := by
    nlinarith [hLoss x]
  have hPnorm : ‖P x‖ ≤ ‖x‖ := by
    calc
      ‖P x‖ ≤ ‖P‖ * ‖x‖ := P.le_opNorm x
      _ ≤ 1 * ‖x‖ :=
        mul_le_mul_of_nonneg_right (IsStarProjection.norm_le P hP) (norm_nonneg x)
      _ = ‖x‖ := one_mul _
  have hSquare : ‖Q (U (P x))‖ ^ 2 ≤ (1 - δ) * ‖x‖ ^ 2 :=
    hRetained.trans (mul_le_mul_of_nonneg_left
      ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hPnorm) hRemaining)
  change ‖Q (U (P x))‖ ≤ Real.sqrt (1 - δ) * ‖x‖
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  simpa only [mul_pow, Real.sq_sqrt hRemaining] using hSquare

/-- A strictly positive complementary energy fraction forces strict
contraction, including when the source Hilbert space is trivial. -/
theorem localization_norm_lt_one_of_leakage (U : E →ₗᵢ[𝕜] F)
    (P : E →L[𝕜] E) (Q : F →L[𝕜] F)
    (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hLoss : ∀ x, δ * ‖P x‖ ^ 2 ≤ ‖(1 - Q) (U (P x))‖ ^ 2) :
    ‖Q ∘L U.toContinuousLinearMap ∘L P‖ < 1 := by
  apply (localization_norm_le_of_leakage U P Q hP hQ hδ1 hLoss).trans_lt
  have hSquare := Real.sq_sqrt (sub_nonneg.mpr hδ1)
  have hRoot := Real.sqrt_nonneg (1 - δ)
  nlinarith [hδ0]

/-- For a projection symbol, the compressed operator is the Gram operator
of the retained part of the isometry. -/
theorem compression_eq_retained_gram (U : E →ₗᵢ[𝕜] F)
    (Q : F →L[𝕜] F) (hQ : IsStarProjection Q) :
    U.toContinuousLinearMap.adjoint ∘L Q ∘L U.toContinuousLinearMap =
      (Q ∘L U.toContinuousLinearMap).adjoint ∘L (Q ∘L U.toContinuousLinearMap) := by
  have hQQ : Q.adjoint ∘L Q = Q := by
    change star Q * Q = Q
    rw [hQ.isSelfAdjoint.star_eq, hQ.isIdempotentElem.eq]
  rw [adjoint_comp, comp_assoc, ← comp_assoc Q.adjoint Q U.toContinuousLinearMap,
    hQQ]

/-- The compressed positive operator has the squared contraction factor.
The missing geometric or Gaussian estimate is exactly `hLoss`. -/
theorem compression_norm_le_of_leakage (U : E →ₗᵢ[𝕜] F)
    (Q : F →L[𝕜] F) (hQ : IsStarProjection Q)
    {δ : ℝ} (hδ : δ ≤ 1)
    (hLoss : ∀ x, δ * ‖x‖ ^ 2 ≤ ‖(1 - Q) (U x)‖ ^ 2) :
    ‖U.toContinuousLinearMap.adjoint ∘L Q ∘L U.toContinuousLinearMap‖ ≤ 1 - δ := by
  have hBound : ‖Q ∘L U.toContinuousLinearMap‖ ≤ Real.sqrt (1 - δ) := by
    simpa only [one_def, comp_id] using
      localization_norm_le_of_leakage U 1 Q (IsStarProjection.one _) hQ hδ
        (by intro x; exact hLoss x)
  rw [compression_eq_retained_gram U Q hQ, norm_adjoint_comp_self, ← pow_two]
  calc
    ‖Q ∘L U.toContinuousLinearMap‖ ^ 2 ≤ (Real.sqrt (1 - δ)) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mpr hBound
    _ = 1 - δ := Real.sq_sqrt (sub_nonneg.mpr hδ)

end InfoGeometry.Analysis.HilbertLocalizationEnergy
