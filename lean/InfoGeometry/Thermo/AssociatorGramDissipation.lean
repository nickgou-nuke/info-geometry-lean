/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic

/-!
# A positive Gram form for projected leakage operators

A finite family of real linear operators `R i`, a real linear map `P`, and a
positive observer form `B` give the bilinear response

`D x y = γ * ∑ i, B (R i (P x)) (R i (P y))`.

Symmetry and nonnegativity follow from the observer form. A direction killed
by `P` is in both radicals of `D`. If `B` is strictly positive and `γ > 0`,
the exact zero-production condition is membership in the common kernel of
the operators `R i ∘ P`. Identifying that common kernel with `ker P` needs
the additional separation hypothesis stated below.

This construction is independent of a Poisson tensor or a choice of entropy.
Its split-octonion specialization supplies actual associator operators and a
nonzero production witness in `Canonical.SplitOctonionAssociatorGram`.
-/

noncomputable section

namespace InfoGeometry.Thermo.AssociatorGramDissipation

open scoped BigOperators

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable {ι : Type*} [Fintype ι]

/-- The native bilinear Gram form of the projected operator family. -/
def gramForm (B : LinearMap.BilinForm ℝ V) (R : ι → Module.End ℝ V)
    (P : Module.End ℝ V) (γ : ℝ) : LinearMap.BilinForm ℝ V :=
  γ • ∑ i, B.compl₁₂ ((R i).comp P) ((R i).comp P)

@[simp] theorem gramForm_apply
    (B : LinearMap.BilinForm ℝ V) (R : ι → Module.End ℝ V)
    (P : Module.End ℝ V) (γ : ℝ) (x y : V) :
    gramForm B R P γ x y = γ * ∑ i, B (R i (P x)) (R i (P y)) := by
  simp only [gramForm, LinearMap.smul_apply, LinearMap.sum_apply,
    LinearMap.compl₁₂_apply, LinearMap.comp_apply, smul_eq_mul]

theorem gramForm_isSymm
    (B : LinearMap.BilinForm ℝ V) (R : ι → Module.End ℝ V)
    (P : Module.End ℝ V) (γ : ℝ) (hB : B.IsSymm) :
    (gramForm B R P γ).IsSymm := by
  refine ⟨fun x y => ?_⟩
  change gramForm B R P γ x y = gramForm B R P γ y x
  rw [gramForm_apply, gramForm_apply]
  apply congrArg (fun t : ℝ => γ * t)
  apply Finset.sum_congr rfl
  intro i _
  exact hB.eq _ _

theorem gramForm_nonneg
    (B : LinearMap.BilinForm ℝ V) (R : ι → Module.End ℝ V)
    (P : Module.End ℝ V) (γ : ℝ)
    (hB : ∀ x : V, 0 ≤ B x x) (hγ : 0 ≤ γ) (x : V) :
    0 ≤ gramForm B R P γ x x := by
  rw [gramForm_apply]
  exact mul_nonneg hγ (Finset.sum_nonneg fun i _ => hB (R i (P x)))

theorem gramForm_isPosSemidef
    (B : LinearMap.BilinForm ℝ V) (R : ι → Module.End ℝ V)
    (P : Module.End ℝ V) (γ : ℝ)
    (hB : B.IsPosSemidef) (hγ : 0 ≤ γ) :
    (gramForm B R P γ).IsPosSemidef where
  isSymm := gramForm_isSymm B R P γ hB.isSymm
  isNonneg := ⟨gramForm_nonneg B R P γ hB.nonneg hγ⟩

/-- A vector in the common leakage kernel is in the left radical. -/
theorem gramForm_eq_zero_of_commonKernel
    (B : LinearMap.BilinForm ℝ V) (R : ι → Module.End ℝ V)
    (P : Module.End ℝ V) (γ : ℝ) (x y : V)
    (hx : ∀ i, R i (P x) = 0) : gramForm B R P γ x y = 0 := by
  rw [gramForm_apply]
  have hsum : ∑ i, B (R i (P x)) (R i (P y)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    simp only [hx i, map_zero, LinearMap.zero_apply]
  rw [hsum, mul_zero]

/-- Projection annihilation gives energy degeneracy in the left slot. -/
theorem gramForm_eq_zero_of_projection_left
    (B : LinearMap.BilinForm ℝ V) (R : ι → Module.End ℝ V)
    (P : Module.End ℝ V) (γ : ℝ) (H x : V) (hH : P H = 0) :
    gramForm B R P γ H x = 0 :=
  gramForm_eq_zero_of_commonKernel B R P γ H x (fun i => by rw [hH, map_zero])

/-- Projection annihilation gives energy degeneracy in the right slot. -/
theorem gramForm_eq_zero_of_projection_right
    (B : LinearMap.BilinForm ℝ V) (R : ι → Module.End ℝ V)
    (P : Module.End ℝ V) (γ : ℝ) (x H : V) (hH : P H = 0) :
    gramForm B R P γ x H = 0 := by
  simp only [gramForm_apply, hH, map_zero, Finset.sum_const_zero, mul_zero]

private theorem nonneg_of_strictPos
    (B : LinearMap.BilinForm ℝ V)
    (hpos : ∀ x : V, x ≠ 0 → 0 < B x x) (x : V) : 0 ≤ B x x := by
  by_cases hx : x = 0
  · subst x
    simp
  · exact (hpos x hx).le

/-- Zero production means every projected leakage operator vanishes. -/
theorem gramForm_self_eq_zero_iff
    (B : LinearMap.BilinForm ℝ V) (R : ι → Module.End ℝ V)
    (P : Module.End ℝ V) (γ : ℝ)
    (hpos : ∀ x : V, x ≠ 0 → 0 < B x x) (hγ : 0 < γ) (x : V) :
    gramForm B R P γ x x = 0 ↔ ∀ i, R i (P x) = 0 := by
  constructor
  · intro hx i
    rw [gramForm_apply] at hx
    have hsum : ∑ j, B (R j (P x)) (R j (P x)) = 0 :=
      (mul_eq_zero.mp hx).resolve_left (ne_of_gt hγ)
    have hi : B (R i (P x)) (R i (P x)) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => nonneg_of_strictPos B hpos (R j (P x)))).mp
          hsum i (Finset.mem_univ i)
    by_contra hne
    exact (ne_of_gt (hpos _ hne)) hi
  · intro hx
    exact gramForm_eq_zero_of_commonKernel B R P γ x x hx

/-- The left radical is exactly the common kernel, without an injectivity assumption. -/
theorem gramForm_left_eq_zero_iff
    (B : LinearMap.BilinForm ℝ V) (R : ι → Module.End ℝ V)
    (P : Module.End ℝ V) (γ : ℝ)
    (hpos : ∀ x : V, x ≠ 0 → 0 < B x x) (hγ : 0 < γ) (x : V) :
    gramForm B R P γ x = 0 ↔ ∀ i, R i (P x) = 0 := by
  constructor
  · intro hx
    apply (gramForm_self_eq_zero_iff B R P γ hpos hγ x).mp
    exact congrArg (fun f : V →ₗ[ℝ] ℝ => f x) hx
  · intro hx
    apply LinearMap.ext
    intro y
    exact gramForm_eq_zero_of_commonKernel B R P γ x y hx

/-- The radical identity in the native submodule lattice. -/
theorem ker_gramForm
    (B : LinearMap.BilinForm ℝ V) (R : ι → Module.End ℝ V)
    (P : Module.End ℝ V) (γ : ℝ)
    (hpos : ∀ x : V, x ≠ 0 → 0 < B x x) (hγ : 0 < γ) :
    LinearMap.ker (gramForm B R P γ) =
      ⨅ i, LinearMap.ker ((R i).comp P) := by
  ext x
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.comp_apply]
  exact gramForm_left_eq_zero_iff B R P γ hpos hγ x

/-- A single nonzero leakage mode is sufficient for strictly positive production. -/
theorem gramForm_self_pos_iff
    (B : LinearMap.BilinForm ℝ V) (R : ι → Module.End ℝ V)
    (P : Module.End ℝ V) (γ : ℝ)
    (hpos : ∀ x : V, x ≠ 0 → 0 < B x x) (hγ : 0 < γ) (x : V) :
    0 < gramForm B R P γ x x ↔ ∃ i, R i (P x) ≠ 0 := by
  classical
  constructor
  · intro hx
    by_contra hnone
    have hzero : ∀ i, R i (P x) = 0 := by
      intro i
      by_contra hi
      exact hnone ⟨i, hi⟩
    exact (ne_of_gt hx) ((gramForm_self_eq_zero_iff B R P γ hpos hγ x).mpr hzero)
  · rintro ⟨i, hi⟩
    have hnonneg := gramForm_nonneg B R P γ (nonneg_of_strictPos B hpos) hγ.le x
    by_contra hnpos
    have hzero : gramForm B R P γ x x = 0 :=
      le_antisymm (le_of_not_gt hnpos) hnonneg
    exact hi ((gramForm_self_eq_zero_iff B R P γ hpos hγ x).mp hzero i)

/-- Equality with `ker P` requires that the family separate vectors in `range P`. -/
theorem gramForm_self_eq_zero_iff_projection_eq_zero
    (B : LinearMap.BilinForm ℝ V) (R : ι → Module.End ℝ V)
    (P : Module.End ℝ V) (γ : ℝ)
    (hpos : ∀ x : V, x ≠ 0 → 0 < B x x) (hγ : 0 < γ)
    (hjoint : ∀ v ∈ LinearMap.range P, (∀ i, R i v = 0) → v = 0)
    (x : V) : gramForm B R P γ x x = 0 ↔ P x = 0 := by
  constructor
  · intro hx
    exact hjoint (P x) ⟨x, rfl⟩
      ((gramForm_self_eq_zero_iff B R P γ hpos hγ x).mp hx)
  · intro hx
    exact gramForm_eq_zero_of_projection_left B R P γ x x hx

end InfoGeometry.Thermo.AssociatorGramDissipation
