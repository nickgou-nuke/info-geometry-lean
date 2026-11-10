/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Tactic

/-!
# ℤ^n → 𝕋 embedding arithmetic seeds

This module records finite coordinate counts and elementary integer arithmetic
associated with a proposed dense embedding. It does not define the embedding,
prove rational independence, or prove injectivity or density.

## Seed values

The stored arithmetic conventions are `generatorCount n = card (Fin n)` and
`qIndepDim n = n + 1`.

The small dimension lemmas below concern only these numerical conventions.

## Paper references

- thm:conclusion-zn-to-circle-injective-dense

## Scope

This file contains finite-index counts and arithmetic seeds. It does not
construct the proposed homomorphism into the circle or prove injectivity,
rational independence, or density.
-/

namespace Omega.Conclusion.ZnToCircleInjectiveDenseSeeds

/-! ## Generator index cardinality -/

/-- Cardinality of the finite coordinate index type for an `n`-coordinate
    integer lattice. This is an index-counting quantity; it does not by itself
    construct or prove a dense homomorphism into the circle. -/
def generatorCount (n : ℕ) : ℕ := Fintype.card (Fin n)

/-- Stored arithmetic convention for the advertised parameter dimension. -/
def qIndepDim (n : ℕ) : ℕ := n + 1

/-- Q-independence dimension seed: n=1 needs 2 Q-independent numbers.
    thm:conclusion-zn-to-circle-injective-dense -/
theorem qIndepDim_1 : qIndepDim 1 = 2 := by simp [qIndepDim]

/-- Q-independence dimension seed: n=2 needs 3 Q-independent numbers.
    thm:conclusion-zn-to-circle-injective-dense -/
theorem qIndepDim_2 : qIndepDim 2 = 3 := by simp [qIndepDim]

/-- Q-independence dimension seed: n=3 needs 4 Q-independent numbers.
    thm:conclusion-zn-to-circle-injective-dense -/
theorem qIndepDim_3 : qIndepDim 3 = 4 := by simp [qIndepDim]

/-- Q-independence dimension seed: n=5 needs 6 Q-independent numbers.
    thm:conclusion-zn-to-circle-injective-dense -/
theorem qIndepDim_5 : qIndepDim 5 = 6 := by simp [qIndepDim]

/-! ## Inner product kernel: ⟨k, α⟩ = 0 ⟹ k = 0

Injectivity of Φ(k) = exp(2πi⟨k, α⟩) reduces to:
if ⟨k, α⟩ ∈ ℤ then k = 0 (by Q-independence).

At integer level, the linear form L(k₁, …, kₙ) = Σ kᵢ · aᵢ
with algebraically independent coefficients aᵢ satisfies L=0 ⟹ all kᵢ=0. -/

/-- Integer linear form in two variables.
    thm:conclusion-zn-to-circle-injective-dense -/
def linearForm2 (a₁ a₂ k₁ k₂ : ℤ) : ℤ := k₁ * a₁ + k₂ * a₂

/-- Linear form vanishes at origin.
    thm:conclusion-zn-to-circle-injective-dense -/
theorem linearForm2_zero (a₁ a₂ : ℤ) : linearForm2 a₁ a₂ 0 0 = 0 := by
  simp [linearForm2]

/-- Linear form is additive in coefficients.
    thm:conclusion-zn-to-circle-injective-dense -/
theorem linearForm2_add (a₁ a₂ k₁ k₂ l₁ l₂ : ℤ) :
    linearForm2 a₁ a₂ (k₁ + l₁) (k₂ + l₂) =
    linearForm2 a₁ a₂ k₁ k₂ + linearForm2 a₁ a₂ l₁ l₂ := by
  simp [linearForm2]; ring

/-- Linear form negation: Φ(k)⁻¹ = Φ(-k).
    thm:conclusion-zn-to-circle-injective-dense -/
theorem linearForm2_neg (a₁ a₂ k₁ k₂ : ℤ) :
    linearForm2 a₁ a₂ (-k₁) (-k₂) = -linearForm2 a₁ a₂ k₁ k₂ := by
  simp [linearForm2]; ring

/-! ## Proposed closed subgroup criterion (not formalized here)

The only closed subgroups of 𝕋 are: finite cyclic groups ℤ/nℤ, or 𝕋 itself.
An infinite subgroup has closure = 𝕋, hence is dense.

The key dichotomy: a subgroup H ≤ 𝕋 satisfies either |H| < ∞ or H̄ = 𝕋.
For Φ(ℤ^n) with n ≥ 1 and Q-independent α, the image is infinite
(since ℤ^n is infinite and Φ is injective), hence dense. -/

/-- The cardinality of the `Fin n` coordinate index is `n`. -/
theorem rank_eq (n : ℕ) : generatorCount n = n := by
  simp [generatorCount]

/-- For n ≥ 1, the group ℤ^n is infinite (rank ≥ 1 suffices).
    At integer level: n ≥ 1 → n > 0.
    thm:conclusion-zn-to-circle-injective-dense -/
theorem pos_rank_of_pos (n : ℕ) (hn : 1 ≤ n) : 0 < generatorCount n := by
  simp [generatorCount]; omega

/-! ## Open circle-density bridge

The closed-subgroup dichotomy and the proposed dense embedding are not
formalized in this arithmetic seed file: it defines no subgroup, homomorphism,
or topology on the circle. -/

/-- The unit group modulo one has one residue class, as reflected by
`Nat.totient 1 = 1`. -/
theorem cyclic_order_1 : Nat.totient 1 = 1 := by norm_num

/-- The actual totient values for the four divisors of six sum to six. -/
theorem totient_sum_6 :
    Nat.totient 1 + Nat.totient 2 + Nat.totient 3 + Nat.totient 6 = 6 := by
  decide

/-- The advertised `n+1` independence count is one more than the finite
    coordinate index count. This arithmetic statement does not assert the
    existence of rationally independent parameters or a circle homomorphism. -/
theorem hom_param_count (n : ℕ) : qIndepDim n = generatorCount n + 1 := by
  simp [qIndepDim, generatorCount]

/-- Arithmetic seed package associated with a proposed ℤⁿ-to-circle result.
    This package does not establish an embedding or a density theorem.
    thm:conclusion-zn-to-circle-injective-dense -/
theorem paper_conclusion_zn_to_circle_injective_dense_seeds :
    qIndepDim 1 = 2 ∧ qIndepDim 2 = 3 ∧ qIndepDim 3 = 4
    ∧ (∀ a₁ a₂ k₁ k₂ l₁ l₂ : ℤ,
      linearForm2 a₁ a₂ (k₁ + l₁) (k₂ + l₂) =
        linearForm2 a₁ a₂ k₁ k₂ + linearForm2 a₁ a₂ l₁ l₂)
    ∧ (∀ n : ℕ, 1 ≤ n → 0 < generatorCount n) := by
  exact ⟨qIndepDim_1, qIndepDim_2, qIndepDim_3,
    linearForm2_add, pos_rank_of_pos⟩

/-- Paper-facing package for the integer seed statements; not an injectivity
    or density conclusion.
    thm:conclusion-qpos-general-singlephase-injective-dense -/
theorem paper_conclusion_qpos_general_singlephase_injective_dense_package :
    qIndepDim 1 = 2 ∧ qIndepDim 2 = 3 ∧ qIndepDim 3 = 4
    ∧ (∀ a₁ a₂ k₁ k₂ l₁ l₂ : ℤ,
      linearForm2 a₁ a₂ (k₁ + l₁) (k₂ + l₂) =
        linearForm2 a₁ a₂ k₁ k₂ + linearForm2 a₁ a₂ l₁ l₂)
    ∧ (∀ n : ℕ, 1 ≤ n → 0 < generatorCount n) :=
  paper_conclusion_zn_to_circle_injective_dense_seeds

end Omega.Conclusion.ZnToCircleInjectiveDenseSeeds
