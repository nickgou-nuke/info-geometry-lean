/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.KitaevChainCoefficients

noncomputable section
namespace InfoGeometry.Canonical.KitaevChainKernel

open Matrix KitaevChainCoefficients
open scoped BigOperators

variable {N : ℕ}

@[simp] theorem bondLeft_eq_iff (j k : Fin (N - 1)) :
    bondLeft j = bondLeft k ↔ j = k := by
  constructor
  · intro h
    apply Fin.ext
    have := congrArg Fin.val h
    simp only [bondLeft] at this
    omega
  · rintro rfl; rfl

@[simp] theorem bondRight_eq_iff (j k : Fin (N - 1)) :
    bondRight j = bondRight k ↔ j = k := by
  constructor
  · intro h
    apply Fin.ext
    have := congrArg Fin.val h
    simp only [bondRight] at this
    omega
  · rintro rfl; rfl

theorem bondLeft_ne_bondRight_any (j k : Fin (N - 1)) :
    bondLeft j ≠ bondRight k := by
  intro h
  have := congrArg Fin.val h
  simp only [bondLeft, bondRight] at this
  omega

/-- Coordinate readout of the actual sparse matrix action. -/
theorem chain_action (t : ℝ) (v : Fin (2 * N) → ℝ) (i : Fin (2 * N)) :
    (chainCoefficientMatrix N t *ᵥ v) i =
      ∑ j : Fin (N - 1),
        ((if i = bondLeft j then 2 * t * v (bondRight j) else 0) -
         (if i = bondRight j then 2 * t * v (bondLeft j) else 0)) := by
  simp [chainCoefficientMatrix, Matrix.sum_mulVec, Matrix.sub_mulVec,
    Matrix.single_mulVec, Function.update_apply]

theorem chain_action_bondLeft (t : ℝ) (v : Fin (2 * N) → ℝ)
    (j : Fin (N - 1)) :
    (chainCoefficientMatrix N t *ᵥ v) (bondLeft j) = 2 * t * v (bondRight j) := by
  rw [chain_action]
  simp [bondLeft_ne_bondRight_any]

theorem chain_action_bondRight (t : ℝ) (v : Fin (2 * N) → ℝ)
    (j : Fin (N - 1)) :
    (chainCoefficientMatrix N t *ᵥ v) (bondRight j) = -(2 * t * v (bondLeft j)) := by
  rw [chain_action]
  have hne : ∀ k : Fin (N - 1), bondRight j ≠ bondLeft k :=
    fun k => (bondLeft_ne_bondRight_any k j).symm
  simp [hne, Finset.sum_neg_distrib]

theorem chain_action_endpoint (t : ℝ) (v : Fin (2 * N) → ℝ)
    (i : Fin (2 * N)) (hi : i.val = 0 ∨ i.val + 1 = 2 * N) :
    (chainCoefficientMatrix N t *ᵥ v) i = 0 := by
  rw [chain_action]
  apply Finset.sum_eq_zero
  intro j _
  have hl : i ≠ bondLeft j := by
    intro h
    have := congrArg Fin.val h
    simp only [bondLeft] at this
    have := j.isLt
    omega
  have hr : i ≠ bondRight j := by
    intro h
    have := congrArg Fin.val h
    simp only [bondRight] at this
    have := j.isLt
    omega
  simp [hl, hr]

theorem chain_kernel_iff_bond_coordinates (t : ℝ) (ht : t ≠ 0)
    (v : Fin (2 * N) → ℝ) :
    chainCoefficientMatrix N t *ᵥ v = 0 ↔
      ∀ j : Fin (N - 1), v (bondLeft j) = 0 ∧ v (bondRight j) = 0 := by
  constructor
  · intro h j
    have hl := congrFun h (bondLeft j)
    have hr := congrFun h (bondRight j)
    rw [chain_action_bondLeft] at hl
    rw [chain_action_bondRight] at hr
    have h2t : 2 * t ≠ 0 := mul_ne_zero (by norm_num) ht
    exact ⟨(mul_eq_zero.mp (neg_eq_zero.mp hr)).resolve_left h2t,
      (mul_eq_zero.mp hl).resolve_left h2t⟩
  · intro h
    funext i
    rw [chain_action]
    apply Finset.sum_eq_zero
    intro j _
    simp [(h j).1, (h j).2]

/-- The bonds exhaust precisely the interior labels, with no endpoint included. -/
theorem interior_bond_coverage (i : Fin (2 * N))
    (hi : 0 < i.val ∧ i.val + 1 < 2 * N) :
    ∃ j : Fin (N - 1), i = bondLeft j ∨ i = bondRight j := by
  let j : Fin (N - 1) := ⟨(i.val - 1) / 2, by omega⟩
  refine ⟨j, ?_⟩
  by_cases he : i.val % 2 = 1
  · left
    apply Fin.ext
    simp only [bondLeft, j]
    omega
  · right
    apply Fin.ext
    simp only [bondRight, j]
    omega

/-- For nonzero coupling the full kernel consists exactly of endpoint coefficients. -/
theorem chain_kernel_iff_interior_zero (t : ℝ) (ht : t ≠ 0)
    (v : Fin (2 * N) → ℝ) :
    chainCoefficientMatrix N t *ᵥ v = 0 ↔
      ∀ i : Fin (2 * N), 0 < i.val ∧ i.val + 1 < 2 * N → v i = 0 := by
  rw [chain_kernel_iff_bond_coordinates t ht]
  constructor
  · intro h i hi
    obtain ⟨j, hl | hr⟩ := interior_bond_coverage i hi
    · rw [hl]; exact (h j).1
    · rw [hr]; exact (h j).2
  · intro h j
    have hj := j.isLt
    constructor
    · apply h
      simp only [bondLeft]
      omega
    · apply h
      simp only [bondRight]
      omega

end InfoGeometry.Canonical.KitaevChainKernel
