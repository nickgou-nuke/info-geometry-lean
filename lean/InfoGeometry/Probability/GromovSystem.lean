import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Field
import Mathlib.Tactic.NormNum

/-!
# Finite staged Gromov algebra, in canonical mathlib notation

This file states finite staged weight identities directly with mathlib's
canonical ingredients: stage-indexed types, finite sums `∑`, cardinalities
`Finset.card`, rational and real division `/`, and explicit bonding maps.
It intentionally defines no proof-carrying `GromovSystem` structure and no local
wrappers for relative volume, ratios, total mass, or normalization.

The results are finite algebraic statements only.  No projective-limit measure,
Radon--Nikodym theorem, Cantor-boundary measure, or asymptotic boundary theorem
is asserted.
-/

set_option autoImplicit false

open scoped BigOperators

namespace GromovSystem

variable {X : ℕ → Type*}

section FiniteRelativeVolume

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- Projection/intersection count never exceeds the ambient finite count. -/
theorem projection_count_le_total (ambient event : Finset α) :
    (ambient ∩ event).card ≤ ambient.card := by
  exact Finset.card_le_card Finset.inter_subset_left

/-- Multiplying the finite rational cardinality ratio by the ambient count recovers the event count. -/
theorem relativeVolume_mul_total_count (ambient event : Finset α)
    (h : ambient.card ≠ 0) :
    (((ambient ∩ event).card : ℚ) / (ambient.card : ℚ)) * (ambient.card : ℚ) =
      ((ambient ∩ event).card : ℚ) := by
  exact div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr h)

/-- The finite rational cardinality ratio is nonnegative. -/
theorem relativeVolume_nonneg (ambient event : Finset α) :
    (0 : ℚ) ≤ ((ambient ∩ event).card : ℚ) / (ambient.card : ℚ) := by
  exact div_nonneg (by exact_mod_cast Nat.zero_le (ambient ∩ event).card)
    (by exact_mod_cast Nat.zero_le ambient.card)

/-- The finite rational cardinality ratio is at most one when the ambient set is nonempty. -/
theorem relativeVolume_le_one (ambient event : Finset α) (h : ambient.card ≠ 0) :
    ((ambient ∩ event).card : ℚ) / (ambient.card : ℚ) ≤ 1 := by
  have hpos : (0 : ℚ) < (ambient.card : ℚ) := by
    exact_mod_cast Nat.pos_of_ne_zero h
  have hle : ((ambient ∩ event).card : ℚ) ≤ (ambient.card : ℚ) := by
    exact_mod_cast projection_count_le_total ambient event
  rw [div_le_one hpos]
  exact hle

/-- The finite rational cardinality ratio lies in the unit interval for nonempty ambient sets. -/
theorem relativeVolume_mem_unit_interval (ambient event : Finset α)
    (h : ambient.card ≠ 0) :
    (0 : ℚ) ≤ ((ambient ∩ event).card : ℚ) / (ambient.card : ℚ) ∧
      ((ambient ∩ event).card : ℚ) / (ambient.card : ℚ) ≤ 1 := by
  exact ⟨relativeVolume_nonneg ambient event, relativeVolume_le_one ambient event h⟩

/-- The finite rational cardinality ratio of the whole nonempty ambient set is one. -/
theorem relativeVolume_self (ambient : Finset α) (h : ambient.card ≠ 0) :
    (((ambient ∩ ambient).card : ℚ) / (ambient.card : ℚ)) = 1 := by
  rw [Finset.inter_self]
  exact div_self (Nat.cast_ne_zero.mpr h)

/-- An event and its ambient complement have finite rational volumes summing to one. -/
theorem relativeVolume_add_complement (ambient event : Finset α)
    (h : ambient.card ≠ 0) :
    ((ambient ∩ event).card : ℚ) / (ambient.card : ℚ) +
        ((ambient ∩ (ambient \ event)).card : ℚ) / (ambient.card : ℚ) =
      1 := by
  have hden : (ambient.card : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr h
  have hinter : ambient ∩ (ambient \ event) = ambient \ event := by
    ext x
    simp
  have hcard :
      (ambient ∩ event).card + (ambient ∩ (ambient \ event)).card = ambient.card := by
    rw [hinter]
    exact Finset.card_inter_add_card_sdiff ambient event
  have hcast :
      ((ambient ∩ event).card : ℚ) + ((ambient ∩ (ambient \ event)).card : ℚ) =
        (ambient.card : ℚ) := by
    exact_mod_cast hcard
  rw [← add_div, hcast]
  exact div_self hden

/-- The finite rational cardinality ratio of the empty event is zero. -/
theorem relativeVolume_empty_event (ambient : Finset α) :
    (((ambient ∩ (∅ : Finset α)).card : ℚ) / (ambient.card : ℚ)) = 0 := by
  have hcard : (ambient ∩ (∅ : Finset α)).card = 0 := by
    rw [Finset.inter_empty]
    rfl
  rw [hcard]
  exact zero_div _

/-- Finite rational cardinality ratios are invariant under relabeling equivalences. -/
theorem relativeVolume_equiv_image (e : α ≃ β) (ambient event : Finset α) :
    ((((ambient.image e) ∩ (event.image e)).card : ℚ) / ((ambient.image e).card : ℚ)) =
      (((ambient ∩ event).card : ℚ) / (ambient.card : ℚ)) := by
  have hnum : ((ambient.image e) ∩ (event.image e)).card = (ambient ∩ event).card := by
    rw [← Finset.image_inter ambient event e.injective]
    exact Finset.card_image_of_injective (ambient ∩ event) e.injective
  have hden : (ambient.image e).card = ambient.card :=
    Finset.card_image_of_injective ambient e.injective
  rw [hnum, hden]

omit [DecidableEq α] in
/-- Multiplying a finite rational average by the sample cardinality recovers the sum. -/
theorem finiteAverage_mul_card (sample : Finset α) (f : α → ℚ)
    (h : sample.card ≠ 0) :
    ((∑ x ∈ sample, f x) / (sample.card : ℚ)) * (sample.card : ℚ) =
      ∑ x ∈ sample, f x := by
  exact div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr h)

omit [DecidableEq α] in
/-- The finite rational average of the constant-one profile over a nonempty sample is one. -/
theorem finiteAverage_one (sample : Finset α) (h : sample.card ≠ 0) :
    ((∑ _x ∈ sample, (1 : ℚ)) / (sample.card : ℚ)) = 1 := by
  have hden : (sample.card : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr h
  rw [Finset.sum_const, nsmul_eq_mul]
  simp [hden]

end FiniteRelativeVolume

/-- Compatible transported weights have the same finite projective ratio. -/
theorem projective_ratio_invariant
    (measure : ∀ n, X n → ℝ) (bond : ∀ n, X n → X (n + 1))
    (compatibility : ∀ n (x : X n), measure (n + 1) (bond n x) = measure n x)
    (n : ℕ) (x y : X n) :
    measure (n + 1) (bond n x) / measure (n + 1) (bond n y) =
      measure n x / measure n y := by
  rw [compatibility n x, compatibility n y]

/--
If a transported nonzero weight is compatible but total mass changes between
finite stages, then normalized ratios cannot commute with the stage map for that
state.
-/
theorem normalization_incompatibility [∀ n, Fintype (X n)]
    (measure : ∀ n, X n → ℝ) (bond : ∀ n, X n → X (n + 1))
    (compatibility : ∀ n (x : X n), measure (n + 1) (bond n x) = measure n x)
    (n : ℕ) (x : X n)
    (h_meas_nz : measure n x ≠ 0)
    (h_sum_n_nz : (∑ y : X n, measure n y) ≠ 0)
    (h_sum_n1_nz : (∑ y : X (n + 1), measure (n + 1) y) ≠ 0)
    (h_sum_change : (∑ y : X (n + 1), measure (n + 1) y) ≠
      (∑ y : X n, measure n y)) :
    measure (n + 1) (bond n x) / (∑ y : X (n + 1), measure (n + 1) y) =
        measure n x / (∑ y : X n, measure n y) → False := by
  intro h_eq
  rw [compatibility n x] at h_eq
  have h_mul :
      (measure n x / (∑ y : X (n + 1), measure (n + 1) y)) *
          ((∑ y : X (n + 1), measure (n + 1) y) * (∑ y : X n, measure n y)) =
        (measure n x / (∑ y : X n, measure n y)) *
          ((∑ y : X (n + 1), measure (n + 1) y) * (∑ y : X n, measure n y)) := by
    rw [h_eq]
  have h_lhs :
      (measure n x / (∑ y : X (n + 1), measure (n + 1) y)) *
          ((∑ y : X (n + 1), measure (n + 1) y) * (∑ y : X n, measure n y)) =
        measure n x * (∑ y : X n, measure n y) := by
    field_simp [h_sum_n1_nz]
  have h_rhs :
      (measure n x / (∑ y : X n, measure n y)) *
          ((∑ y : X (n + 1), measure (n + 1) y) * (∑ y : X n, measure n y)) =
        measure n x * (∑ y : X (n + 1), measure (n + 1) y) := by
    field_simp [h_sum_n_nz]
  rw [h_lhs, h_rhs] at h_mul
  have h_sum_eq :
      (∑ y : X n, measure n y) = (∑ y : X (n + 1), measure (n + 1) y) := by
    exact mul_left_cancel₀ h_meas_nz h_mul
  exact h_sum_change h_sum_eq.symm

end GromovSystem
