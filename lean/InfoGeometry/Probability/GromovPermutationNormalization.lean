/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Data.Set.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Logic.Equiv.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-!
# Finite permutation action and secondary normalization

This file uses mathlib's canonical `Set.image`, equivalences, and real division
notation directly.  It avoids local wrappers for normalization or measure
structures.

The statements are finite/projective algebra facts only: no analytic
concentration theorem, projective-limit measure, or Radon--Nikodym boundary
construction is asserted.
-/

set_option autoImplicit false

namespace InfoGeometry.Probability.GromovPermutationNormalization

/-- The identity permutation acts trivially on subsets of the finite state space. -/
theorem permute_set_identity {n : ℕ} {V : Type*} (U : Set (Fin n → V)) :
    (fun f : Fin n → V => f ∘ (1 : Equiv.Perm (Fin n)).symm) '' U = U := by
  ext f
  constructor
  · intro hf
    rcases hf with ⟨g, hgU, hgf⟩
    simpa using hgf ▸ hgU
  · intro hf
    exact ⟨f, hf, by rfl⟩

/-- Common nonzero scaling cancels under secondary normalization by real division. -/
theorem normalization_projective_scaling (W total c : ℝ)
    (hc : c ≠ 0) :
    (c * W) / (c * total) = W / total := by
  rw [mul_div_mul_left W total hc]

/-! The positive replacement is mass-weighted pooling. Numerators attached to
zero-mass components must vanish; no division by a zero component is cancelled.
The algebraic identity itself remains valid when the total mass is zero. -/

open scoped BigOperators

/-- Pooling and normalization commute through mass-weighted mixture, rather
than through unweighted addition. -/
theorem normalization_sum_eq_mass_mixture {ι : Type*} [Fintype ι]
    (W mass : ι → ℝ) (hzero : ∀ i, mass i = 0 → W i = 0) :
    (∑ i, W i) / (∑ i, mass i) =
      ∑ i, (mass i / (∑ j, mass j)) * (W i / mass i) := by
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : mass i = 0
  · simp [hi, hzero i hi]
  · rw [div_mul_div_comm,
      mul_comm (∑ j, mass j) (mass i), mul_div_mul_left _ _ hi]

/-- Positive total mass turns the pooling coefficients into a probability
vector. Zero-mass components simply receive weight zero. -/
theorem mass_mixture_weights_probability {ι : Type*} [Fintype ι]
    (mass : ι → ℝ) (hmass : ∀ i, 0 ≤ mass i) (htotal : 0 < ∑ i, mass i) :
    (∀ i, 0 ≤ mass i / (∑ j, mass j)) ∧
      (∑ i, mass i / (∑ j, mass j)) = 1 := by
  refine ⟨fun i => div_nonneg (hmass i) (le_of_lt htotal), ?_⟩
  rw [← Finset.sum_div, div_self (ne_of_gt htotal)]

/-- For nonnegative component weights, a component of zero mass has every
entry zero, so mass-weighted pooling applies without excluding empty blocks. -/
theorem normalization_pooled_nonnegative_weights
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (w : κ → ι → ℝ) (hw : ∀ k i, 0 ≤ w k i) (i : ι) :
    (∑ k, w k i) / (∑ k, ∑ j, w k j) =
      ∑ k, ((∑ j, w k j) / (∑ l, ∑ j, w l j)) *
        (w k i / (∑ j, w k j)) := by
  apply normalization_sum_eq_mass_mixture
  intro k hk
  have hle : w k i ≤ ∑ j, w k j :=
    Finset.single_le_sum (fun j _ => hw k j) (Finset.mem_univ i)
  exact le_antisymm (hk ▸ hle) (hw k i)

/-- Concrete finite counterexample: secondary normalization is not additive. -/
theorem normalization_non_additive_counterexample :
    (1 + 1 : ℝ) / (2 + 3) ≠ (1 : ℝ) / 2 + (1 : ℝ) / 3 := by
  norm_num

end InfoGeometry.Probability.GromovPermutationNormalization
