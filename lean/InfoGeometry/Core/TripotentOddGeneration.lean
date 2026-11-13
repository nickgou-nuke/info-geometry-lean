/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.TripotentEigenspaces
import Mathlib.Algebra.Algebra.Operations

/-!
# Exact spans of the odd tripotent anticommutators

For either degree `1` or degree `-1`, the real span of anticommutators is
exactly the native product of the two successive corner submodules through
the zero-mode projector. Submodule multiplication means finite sums of
ordered products. No assertion of surjectivity of a single anticommutator
or of a full Morita equivalence is made.

The carrier is an arbitrary associative real algebra. The two signs follow
from the same submodule argument and the owned Peirce orthogonality laws.
-/

namespace InfoGeometry.Core.TripotentAdjoint

open InfoGeometry.Physics.Algebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {A : Type*} [Ring A] [Algebra ℝ A]

private theorem span_anticommutators_sup_eq_mul (U V : Submodule ℝ A)
    (hUU : ∀ x ∈ U, ∀ y ∈ U, x * y = 0)
    (hVV : ∀ x ∈ V, ∀ y ∈ V, x * y = 0)
    (hVU : ∀ x ∈ V, ∀ y ∈ U, x * y = 0) :
    Submodule.span ℝ
        {z : A | ∃ x ∈ U ⊔ V, ∃ y ∈ U ⊔ V, z = x * y + y * x} = U * V := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro z ⟨x, hx, y, hy, rfl⟩
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨u', hu', v', hv', rfl⟩ := Submodule.mem_sup.mp hy
    have hexpand :
        (u + v) * (u' + v') + (u' + v') * (u + v) = u * v' + u' * v := by
      simp only [add_mul, mul_add, hUU u hu u' hu', hUU u' hu' u hu,
        hVV v hv v' hv', hVV v' hv' v hv, hVU v hv u' hu', hVU v' hv' u hu,
        zero_add, add_zero]
    rw [hexpand]
    exact (U * V).add_mem (Submodule.mul_mem_mul hu hv')
      (Submodule.mul_mem_mul hu' hv)
  · apply Submodule.mul_le.mpr
    intro x hx y hy
    have hanti : x * y + y * x ∈ Submodule.span ℝ
        {z : A | ∃ x ∈ U ⊔ V, ∃ y ∈ U ⊔ V, z = x * y + y * x} :=
      Submodule.subset_span ⟨x, le_sup_left hx, y, le_sup_right hy, rfl⟩
    simpa only [hVU y hy x hx, add_zero] using hanti

/-- Products of two joint corner ranges vanish when the touching Peirce
labels differ. This is multiplication of elements, not composition of the
two corner projectors. -/
theorem mul_eq_zero_of_mem_jointPeirceRanges {S x y : A} (hS : S * S * S = S)
    {a b c d : PeirceSign} (hbc : b ≠ c)
    (hx : x ∈ LinearMap.range (jointPeirceProjector S a b))
    (hy : y ∈ LinearMap.range (jointPeirceProjector S c d)) : x * y = 0 := by
  obtain ⟨u, rfl⟩ := hx
  obtain ⟨v, rfl⟩ := hy
  calc
    jointPeirceProjector S a b u * jointPeirceProjector S c d v =
        peirceProjector S a * u *
          (peirceProjector S b * peirceProjector S c) * v * peirceProjector S d := by
      simp only [jointPeirceProjector_apply, mul_assoc]
    _ = 0 := by
      rw [peirceProjector_mul_eq_zero_of_ne hS hbc]
      simp

/-- The product of successive corners is the ordered sandwich through the
zero-mode projector, with one middle projector after idempotent reduction. -/
theorem jointPeirce_through_zero_product {S : A} (hS : S * S * S = S)
    (a b : PeirceSign) (x y : A) :
    jointPeirceProjector S a .zero x * jointPeirceProjector S .zero b y =
      peirceProjector S a * x * projZero S * y * peirceProjector S b := by
  calc
    jointPeirceProjector S a .zero x * jointPeirceProjector S .zero b y =
        peirceProjector S a * x * (projZero S * projZero S) * y *
          peirceProjector S b := by
      simp only [jointPeirceProjector_apply, peirceProjector_zero, mul_assoc]
    _ = _ := by rw [projZero_idempotent hS]

/-- Degree `1` is exactly the sum of its two successive joint corner ranges. -/
theorem adGrade_one_eq_sup_jointPeirceRanges {S : A} (hS : S * S * S = S) :
    adGrade S 1 =
      LinearMap.range (jointPeirceProjector S .pos .zero) ⊔
        LinearMap.range (jointPeirceProjector S .zero .neg) := by
  have hgrade : adGrade S 1 = fiveGradeRange S .posOne := by
    simp only [adGrade_eq_eigenspace, fiveGradeRange_eq_eigenspace hS, fiveGradeValue]
  apply le_antisymm
  · intro x hx
    rw [hgrade] at hx
    have hfix := (mem_fiveGradeRange_iff_projector_fixed hS .posOne).mp hx
    change jointPeirceProjector S .pos .zero x +
      jointPeirceProjector S .zero .neg x = x at hfix
    exact Submodule.mem_sup.mpr
      ⟨jointPeirceProjector S .pos .zero x, ⟨x, rfl⟩,
        jointPeirceProjector S .zero .neg x, ⟨x, rfl⟩, hfix⟩
  · apply sup_le
    · rintro x ⟨y, rfl⟩
      rw [mem_adGrade_iff]
      simpa [peirceScalar] using
        jointPeirceProjector_adjoint_weight hS .pos .zero y
    · rintro x ⟨y, rfl⟩
      rw [mem_adGrade_iff]
      simpa [peirceScalar] using
        jointPeirceProjector_adjoint_weight hS .zero .neg y

/-- Degree `-1` is the sum of the two corners ordered from the negative
sector through the zero sector to the positive sector. -/
theorem adGrade_neg_one_eq_sup_jointPeirceRanges {S : A} (hS : S * S * S = S) :
    adGrade S (-1) =
      LinearMap.range (jointPeirceProjector S .neg .zero) ⊔
        LinearMap.range (jointPeirceProjector S .zero .pos) := by
  have hgrade : adGrade S (-1) = fiveGradeRange S .negOne := by
    simp only [adGrade_eq_eigenspace, fiveGradeRange_eq_eigenspace hS, fiveGradeValue]
  apply le_antisymm
  · intro x hx
    rw [hgrade] at hx
    have hfix := (mem_fiveGradeRange_iff_projector_fixed hS .negOne).mp hx
    change jointPeirceProjector S .zero .pos x +
      jointPeirceProjector S .neg .zero x = x at hfix
    apply Submodule.mem_sup.mpr
    refine ⟨jointPeirceProjector S .neg .zero x, ⟨x, rfl⟩,
      jointPeirceProjector S .zero .pos x, ⟨x, rfl⟩, ?_⟩
    simpa only [add_comm] using hfix
  · apply sup_le
    · rintro x ⟨y, rfl⟩
      rw [mem_adGrade_iff]
      simpa [peirceScalar] using
        jointPeirceProjector_adjoint_weight hS .neg .zero y
    · rintro x ⟨y, rfl⟩
      rw [mem_adGrade_iff]
      simpa [peirceScalar] using
        jointPeirceProjector_adjoint_weight hS .zero .pos y

/-- The span of positive odd anticommutators is exactly the product of
the two positive directed corner submodules through `P₀`. -/
theorem span_adGrade_one_anticommutators_eq_corner_product {S : A}
    (hS : S * S * S = S) :
    Submodule.span ℝ
        {z : A | ∃ x ∈ adGrade S 1, ∃ y ∈ adGrade S 1, z = x * y + y * x} =
      LinearMap.range (jointPeirceProjector S .pos .zero) *
        LinearMap.range (jointPeirceProjector S .zero .neg) := by
  rw [adGrade_one_eq_sup_jointPeirceRanges hS]
  apply span_anticommutators_sup_eq_mul
  · intro x hx y hy
    exact mul_eq_zero_of_mem_jointPeirceRanges hS (b := .zero) (c := .pos)
      (by decide) hx hy
  · intro x hx y hy
    exact mul_eq_zero_of_mem_jointPeirceRanges hS (b := .neg) (c := .zero)
      (by decide) hx hy
  · intro x hx y hy
    exact mul_eq_zero_of_mem_jointPeirceRanges hS (b := .neg) (c := .pos)
      (by decide) hx hy

/-- The same span identity holds with the direction of both corners reversed. -/
theorem span_adGrade_neg_one_anticommutators_eq_corner_product {S : A}
    (hS : S * S * S = S) :
    Submodule.span ℝ
        {z : A | ∃ x ∈ adGrade S (-1), ∃ y ∈ adGrade S (-1), z = x * y + y * x} =
      LinearMap.range (jointPeirceProjector S .neg .zero) *
        LinearMap.range (jointPeirceProjector S .zero .pos) := by
  rw [adGrade_neg_one_eq_sup_jointPeirceRanges hS]
  apply span_anticommutators_sup_eq_mul
  · intro x hx y hy
    exact mul_eq_zero_of_mem_jointPeirceRanges hS (b := .zero) (c := .neg)
      (by decide) hx hy
  · intro x hx y hy
    exact mul_eq_zero_of_mem_jointPeirceRanges hS (b := .pos) (c := .zero)
      (by decide) hx hy
  · intro x hx y hy
    exact mul_eq_zero_of_mem_jointPeirceRanges hS (b := .pos) (c := .neg)
      (by decide) hx hy

/-- Positive odd anticommutators generate the entire extreme grade exactly
when finite sums of products through the zero sector fill its corner. -/
theorem span_adGrade_one_anticommutators_eq_two_iff {S : A}
    (hS : S * S * S = S) :
    (Submodule.span ℝ
        {z : A | ∃ x ∈ adGrade S 1, ∃ y ∈ adGrade S 1, z = x * y + y * x} =
      adGrade S 2) ↔
      LinearMap.range (jointPeirceProjector S .pos .zero) *
          LinearMap.range (jointPeirceProjector S .zero .neg) =
        LinearMap.range (jointPeirceProjector S .pos .neg) := by
  rw [span_adGrade_one_anticommutators_eq_corner_product hS]
  have hgrade : adGrade S 2 = fiveGradeRange S .posTwo := by
    simp only [adGrade_eq_eigenspace, fiveGradeRange_eq_eigenspace hS, fiveGradeValue]
  simp only [hgrade, fiveGradeRange, fiveGradeProjector, gradePosTwoProjector]

/-- Negative odd anticommutators generate the opposite extreme grade exactly
under the reversed finite-sum factorization condition. -/
theorem span_adGrade_neg_one_anticommutators_eq_neg_two_iff {S : A}
    (hS : S * S * S = S) :
    (Submodule.span ℝ
        {z : A | ∃ x ∈ adGrade S (-1), ∃ y ∈ adGrade S (-1), z = x * y + y * x} =
      adGrade S (-2)) ↔
      LinearMap.range (jointPeirceProjector S .neg .zero) *
          LinearMap.range (jointPeirceProjector S .zero .pos) =
        LinearMap.range (jointPeirceProjector S .neg .pos) := by
  rw [span_adGrade_neg_one_anticommutators_eq_corner_product hS]
  have hgrade : adGrade S (-2) = fiveGradeRange S .negTwo := by
    simp only [adGrade_eq_eigenspace, fiveGradeRange_eq_eigenspace hS, fiveGradeValue]
  simp only [hgrade, fiveGradeRange, fiveGradeProjector, gradeNegTwoProjector]

end InfoGeometry.Core.TripotentAdjoint
