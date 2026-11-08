/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# A contractible fiber of Hamiltonians with a fixed ground space

For an orthogonally complemented subspace `K`, this file considers bounded
symmetric real operators that vanish on `K` and have a fixed quadratic lower
bound on its orthogonal complement. The fiber is convex, contains the scaled
orthogonal-complement projection, and is a contractible topological space.
When the bound is strictly positive, the full kernel is exactly `K`.

The topology is the native operator-norm topology. No commutation between
different Hamiltonians in the fiber is assumed. This result concerns one
fixed ground space and one fixed lower bound; it does not classify the space
obtained by varying the ground space.
-/

noncomputable section

namespace InfoGeometry.Analysis.FixedGroundHamiltonianFiber

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Symmetric bounded operators killing `K` and bounded below by `δ` on `Kᗮ`. -/
def fixedGroundFiber (K : Submodule ℝ E) [K.HasOrthogonalProjection]
    (δ : ℝ) : Set (E →L[ℝ] E) :=
  {H | H.IsSymmetric ∧ (∀ x ∈ K, H x = 0) ∧
    ∀ x, δ * ‖x - K.starProjection x‖ ^ 2 ≤ inner ℝ x (H x)}

variable (K : Submodule ℝ E) [K.HasOrthogonalProjection] (δ : ℝ)

/-- The lower bound and fixed-ground-space conditions survive arbitrary convex
combinations, without a commutation hypothesis. -/
theorem convex_fixedGroundFiber : Convex ℝ (fixedGroundFiber K δ) := by
  intro H₀ h₀ H₁ h₁ a b ha hb hab
  refine ⟨(h₀.1.smul (by simp)).add (h₁.1.smul (by simp)), ?_, ?_⟩
  · intro x hx
    simp only [add_apply, smul_apply,
      h₀.2.1 x hx, h₁.2.1 x hx, smul_zero, add_zero]
  · intro x
    have h := add_le_add (mul_le_mul_of_nonneg_left (h₀.2.2 x) ha)
      (mul_le_mul_of_nonneg_left (h₁.2.2 x) hb)
    calc
      δ * ‖x - K.starProjection x‖ ^ 2 =
          a * (δ * ‖x - K.starProjection x‖ ^ 2) +
          b * (δ * ‖x - K.starProjection x‖ ^ 2) := by
        rw [← add_mul, hab, one_mul]
      _ ≤ a * inner ℝ x (H₀ x) + b * inner ℝ x (H₁ x) := h
      _ = inner ℝ x ((a • H₀ + b • H₁) x) := by
        simp only [add_apply, smul_apply,
          inner_add_right, real_inner_smul_right]

private theorem inner_complement_projection (x : E) :
    inner ℝ x (x - K.starProjection x) = ‖x - K.starProjection x‖ ^ 2 := by
  have h := Kᗮ.re_inner_starProjection_eq_normSq x
  change inner ℝ (Kᗮ.starProjection x) x = ‖Kᗮ.starProjection x‖ ^ 2 at h
  simpa only [Submodule.starProjection_orthogonal_val, real_inner_comm] using h

/-- The scaled projection onto the excited subspace realizes the prescribed
lower bound exactly, so the fiber is nonempty even in infinite dimension. -/
theorem scaled_complement_projection_mem :
    δ • (1 - K.starProjection) ∈ fixedGroundFiber K δ := by
  refine ⟨((LinearMap.IsSymmetric.one).sub K.starProjection_isSymmetric).smul
    (by simp), ?_, ?_⟩
  · intro x hx
    simp only [smul_apply, sub_apply,
      one_apply_eq_self, K.starProjection_eq_self_iff.mpr hx,
      sub_self, smul_zero]
  · intro x
    simp only [smul_apply, sub_apply,
      one_apply_eq_self, real_inner_smul_right,
      inner_complement_projection K]
    exact le_rfl

/-- Nonemptiness is supplied by a concrete bounded operator. -/
theorem fixedGroundFiber_nonempty : (fixedGroundFiber K δ).Nonempty :=
  ⟨δ • (1 - K.starProjection), scaled_complement_projection_mem K δ⟩

/-- Native convex contraction gives an actual homotopy to a point in the
operator-norm topology on the fiber. -/
theorem fixedGroundFiber_contractible : ContractibleSpace (fixedGroundFiber K δ) :=
  (convex_fixedGroundFiber K δ).contractibleSpace (fixedGroundFiber_nonempty K δ)

/-- The affine interpolation of two members keeps the entire lower bound. -/
theorem interpolation_mem {H₀ H₁ : E →L[ℝ] E}
    (h₀ : H₀ ∈ fixedGroundFiber K δ) (h₁ : H₁ ∈ fixedGroundFiber K δ)
    {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    (1 - t) • H₀ + t • H₁ ∈ fixedGroundFiber K δ :=
  convex_fixedGroundFiber K δ h₀ h₁ (sub_nonneg.mpr ht₁) ht₀ (sub_add_cancel 1 t)

/-- A nonnegative gap bound makes every operator in the fiber positive. -/
theorem isPositive_of_mem {H : E →L[ℝ] E}
    (hH : H ∈ fixedGroundFiber K δ) (hδ : 0 ≤ δ) : H.IsPositive := by
  refine ⟨hH.1, fun x => ?_⟩
  have h := (mul_nonneg hδ (sq_nonneg ‖x - K.starProjection x‖)).trans (hH.2.2 x)
  simpa only [ContinuousLinearMap.reApplyInnerSelf_apply, RCLike.re_to_real,
    real_inner_comm] using h

/-- A strictly positive bound excludes every additional zero-energy vector. -/
theorem ker_eq_of_mem {H : E →L[ℝ] E}
    (hH : H ∈ fixedGroundFiber K δ) (hδ : 0 < δ) :
    H.toLinearMap.ker = K := by
  ext x
  constructor
  · intro hx
    have hx0 : H x = 0 := hx
    have hbound := hH.2.2 x
    rw [hx0, inner_zero_right] at hbound
    have hn : ‖x - K.starProjection x‖ ^ 2 = 0 := by
      nlinarith [hδ, sq_nonneg ‖x - K.starProjection x‖]
    have hdiff : x - K.starProjection x = 0 :=
      norm_eq_zero.mp (sq_eq_zero_iff.mp hn)
    exact K.starProjection_eq_self_iff.mp (sub_eq_zero.mp hdiff).symm
  · intro hx
    exact hH.2.1 x hx

/-- On the actual excited subspace, the fiber inequality is the usual
quadratic coercivity estimate. -/
theorem lower_bound_on_orthogonal {H : E →L[ℝ] E}
    (hH : H ∈ fixedGroundFiber K δ) {x : E} (hx : x ∈ Kᗮ) :
    δ * ‖x‖ ^ 2 ≤ inner ℝ x (H x) := by
  simpa only [K.starProjection_apply_eq_zero_iff.mpr hx, sub_zero] using hH.2.2 x

end InfoGeometry.Analysis.FixedGroundHamiltonianFiber
