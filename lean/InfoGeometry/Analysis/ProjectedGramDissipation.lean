/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Projected Gram dissipation on a positive real Hilbert space

This owner constructs the energy constraint from Mathlib's orthogonal projection
and the dissipation operator from actual bounded maps. It does not assume the
desired positivity or energy-kernel laws. The maps may be associator maps after
a separate identification with a chosen positive inner-product carrier.

The split composition norm is not a positivity witness. No differential flow,
Poisson Jacobi law, Gibbs normalization, or Landauer heat bound is asserted.
-/

noncomputable section

open scoped InnerProduct InnerProductSpace BigOperators

namespace InfoGeometry.Analysis.ProjectedGramDissipation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Native orthogonal projection onto the complement of the energy direction.
For the zero direction this is the identity. -/
def energyProjection (h : H) : H →L[ℝ] H :=
  (Submodule.span ℝ ({h} : Set H))ᗮ.starProjection

theorem energyProjection_apply (h x : H) :
    energyProjection h x = x - (⟪h, x⟫_ℝ / ‖h‖ ^ 2) • h := by
  rw [energyProjection, Submodule.starProjection_orthogonal_val,
    Submodule.starProjection_singleton]
  norm_cast

@[simp] theorem energyProjection_self (h : H) : energyProjection h h = 0 :=
  Submodule.starProjection_orthogonalComplement_singleton_eq_zero h

@[simp] theorem energyProjection_zero :
    energyProjection (0 : H) = ContinuousLinearMap.id ℝ H := by
  ext x
  simp [energyProjection_apply]

variable [CompleteSpace H] {F ι : Type*}
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] [Fintype ι]

/-- A finite sum of the actual constrained Gram operators. -/
def dissipator (γ : ℝ) (h : H) (R : ι → H →L[ℝ] F) : H →L[ℝ] H :=
  γ • ∑ i, (R i ∘L energyProjection h)† ∘L (R i ∘L energyProjection h)

/-- The construction is the projected sandwich of the unprojected Gram sum. -/
theorem dissipator_eq_sandwich (γ : ℝ) (h : H) (R : ι → H →L[ℝ] F) :
    dissipator γ h R =
      γ • ((energyProjection h)† ∘L (∑ i, (R i)† ∘L R i) ∘L energyProjection h) := by
  unfold dissipator
  congr 1
  simp only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_assoc,
    ContinuousLinearMap.comp_finsetSum, ContinuousLinearMap.finsetSum_comp]

theorem dissipator_isPositive (γ : ℝ) (hγ : 0 ≤ γ) (h : H)
    (R : ι → H →L[ℝ] F) : (dissipator γ h R).IsPositive := by
  apply ContinuousLinearMap.IsPositive.smul_of_nonneg _ hγ
  exact ContinuousLinearMap.isPositive_sum Finset.univ
    (fun i _ => ContinuousLinearMap.isPositive_adjoint_comp_self
      (R i ∘L energyProjection h))

/-- The bilinear pairing exposes each constrained map without commuting operators. -/
theorem inner_dissipator (γ : ℝ) (h : H) (R : ι → H →L[ℝ] F) (x y : H) :
    ⟪x, dissipator γ h R y⟫_ℝ =
      γ * ∑ i, ⟪R i (energyProjection h x), R i (energyProjection h y)⟫_ℝ := by
  simp only [dissipator, smul_apply, sum_apply, real_inner_smul_right, inner_sum,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]

theorem inner_dissipator_swap (γ : ℝ) (h : H) (R : ι → H →L[ℝ] F) (x y : H) :
    ⟪x, dissipator γ h R y⟫_ℝ = ⟪y, dissipator γ h R x⟫_ℝ := by
  rw [inner_dissipator, inner_dissipator]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact real_inner_comm _ _

theorem inner_dissipator_self (γ : ℝ) (h : H) (R : ι → H →L[ℝ] F) (x : H) :
    ⟪x, dissipator γ h R x⟫_ℝ =
      γ * ∑ i, ‖R i (energyProjection h x)‖ ^ 2 := by
  simp only [inner_dissipator, real_inner_self_eq_norm_sq]

@[simp] theorem dissipator_energy (γ : ℝ) (h : H) (R : ι → H →L[ℝ] F) :
    dissipator γ h R h = 0 := by
  simp [dissipator, ContinuousLinearMap.comp_apply]

theorem inner_dissipator_self_nonneg (γ : ℝ) (hγ : 0 ≤ γ) (h : H)
    (R : ι → H →L[ℝ] F) (x : H) : 0 ≤ ⟪x, dissipator γ h R x⟫_ℝ := by
  rw [inner_dissipator_self]
  exact mul_nonneg hγ (Finset.sum_nonneg (fun i _ => sq_nonneg _))

/-- At nonzero rate, zero quadratic value means that every projected map vanishes
on the given direction. Membership of that direction in a proposed associative
subspace alone does not supply these hypotheses. -/
theorem inner_dissipator_self_eq_zero_iff (γ : ℝ) (hγ : γ ≠ 0) (h : H)
    (R : ι → H →L[ℝ] F) (x : H) :
    ⟪x, dissipator γ h R x⟫_ℝ = 0 ↔ ∀ i, R i (energyProjection h x) = 0 := by
  rw [inner_dissipator_self]
  constructor
  · intro hzero i
    have hsum := (mul_eq_zero.mp hzero).resolve_left hγ
    have hi : ‖R i (energyProjection h x)‖ ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg
        ‖R j (energyProjection h x)‖)).mp hsum i (Finset.mem_univ i)
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hi)
  · intro hzero
    simp [hzero]

theorem dissipator_apply_eq_zero_iff (γ : ℝ) (hγ : γ ≠ 0) (h : H)
    (R : ι → H →L[ℝ] F) (x : H) :
    dissipator γ h R x = 0 ↔ ∀ i, R i (energyProjection h x) = 0 := by
  constructor
  · intro hzero
    apply (inner_dissipator_self_eq_zero_iff γ hγ h R x).mp
    rw [hzero, inner_zero_right]
  · intro hzero
    simp [dissipator, ContinuousLinearMap.comp_apply, hzero]

end InfoGeometry.Analysis.ProjectedGramDissipation
