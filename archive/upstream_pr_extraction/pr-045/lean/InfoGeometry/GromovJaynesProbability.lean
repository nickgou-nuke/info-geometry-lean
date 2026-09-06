import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Rat.Lemmas
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Factorial.Basic

/-!
# Finite Gromov--Jaynes combinatorial probability, canonical surface

This module records finite counting facts directly with mathlib's canonical
finite-set cardinality, finite preimages by `Finset.filter`, rational division,
function-space cardinality, and factorials.

No local measure, projective-measure, normalization, inductive-volume, or
multiplicity wrapper is introduced.  No Stirling bound, entropy limit,
observable-distance concentration theorem, measure-theoretic probability space,
symmetric-group quotient, or analytic large-number limit is asserted.
-/

set_option autoImplicit false

namespace InfoGeometry.GromovJaynesProbability

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

omit [Fintype Ω] in
/-- Additivity of cardinality on disjoint finite sets. -/
theorem gromov_measure_disjoint_union (S T : Finset Ω) (h : Disjoint S T) :
    (S ∪ T).card = S.card + T.card := by
  exact Finset.card_union_of_disjoint h

omit [DecidableEq Ω] in
/-- Filtering by the full codomain preserves total finite cardinality. -/
theorem projective_measure_conservation {Γ : Type*} [Fintype Γ] [DecidableEq Γ]
    (π : Ω → Γ) :
    (Finset.univ.filter (fun x : Ω => π x ∈ (Finset.univ : Finset Γ))).card =
      (Finset.univ : Finset Ω).card := by
  congr 1
  ext x
  simp

omit [DecidableEq Ω] in
/-- If the finite base space is nonempty, the rational cardinality ratio is at most `1`. -/
theorem secondary_normalization_bound (S : Finset Ω)
    (h_nonempty : 0 < (Finset.univ : Finset Ω).card) :
    (S.card : ℚ) / ((Finset.univ : Finset Ω).card : ℚ) ≤ 1 := by
  have hle : (S.card : ℚ) ≤ (((Finset.univ : Finset Ω).card : ℕ) : ℚ) := by
    exact_mod_cast (Finset.card_le_univ S)
  have hden : (0 : ℚ) ≤ (((Finset.univ : Finset Ω).card : ℕ) : ℚ) := by
    exact le_of_lt (Rat.natCast_pos.mpr h_nonempty)
  exact div_le_one_of_le₀ hle hden

/-- Exact finite product-state count for functions from `Fin n`. -/
theorem inductive_product_state_counting {Base : Type*} [Fintype Base] (n : ℕ) :
    Fintype.card (Fin n → Base) = Fintype.card Base ^ n := by
  exact Fintype.card_pi_const Base n

/-- The factorial denominator of a finite class-count profile is positive. -/
theorem multinomial_denominator_pos (class_counts : List ℕ) :
    0 < (class_counts.map Nat.factorial).prod := by
  induction class_counts with
  | nil =>
      simp
  | cons a as ih =>
      simp [Nat.factorial_pos, ih]

end InfoGeometry.GromovJaynesProbability
