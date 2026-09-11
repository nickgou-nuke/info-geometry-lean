import Mathlib.Data.Fintype.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.GroupTheory.Perm.Basic

/-!
# Finite Gromov-style configuration counting, canonical surface

This file states the finite combinatorial core directly with mathlib's
canonical objects:

* configurations are functions `Fin N → X`;
* coordinate permutations are `Equiv.Perm (Fin N)` used by precomposition;
* state counts are `Finset.card` of filtered coordinate sets;
* orbit and fiber statements use `Finset.image` and `Finset.filter` directly;
* projection footprints use `Finset.image` directly;
* the multinomial-style expression and secondary ratio are written inline.

No custom configuration, count-profile, orbit, fiber, projection-footprint,
normalization, or orbit-size wrapper definitions are introduced.  No Stirling
estimate, entropy limit, measure-theoretic probability space, large-deviation
theorem, or analytic concentration limit is asserted.
-/

set_option autoImplicit false

open Finset
open scoped BigOperators

namespace Gromov.Probability

universe u

variable {X : Type u} [Fintype X] [DecidableEq X]

omit [Fintype X] in
/-- Indicator-sum form of a finite state count. -/
theorem state_count_eq_sum_indicator (x : X) {N : ℕ} (f : Fin N → X) :
    (univ.filter (fun i : Fin N => f i = x)).card =
      ∑ i : Fin N, if f i = x then 1 else 0 := by
  simp

omit [Fintype X] in
/-- Subtype-cardinality form of a finite state count. -/
theorem state_count_eq_card_subtype (x : X) {N : ℕ} (f : Fin N → X) :
    (univ.filter (fun i : Fin N => f i = x)).card = Fintype.card {i : Fin N // f i = x} := by
  simp [Fintype.card_subtype]

omit [Fintype X] in
/-- One-step decomposition into tail plus last coordinate. -/
theorem state_count_succ
    (x : X) {N : ℕ} (f : Fin (N + 1) → X) :
    (univ.filter (fun i : Fin (N + 1) => f i = x)).card =
      (univ.filter (fun i : Fin N => f (Fin.castSucc i) = x)).card +
        if f (Fin.last N) = x then 1 else 0 := by
  rw [state_count_eq_sum_indicator]
  rw [Fin.sum_univ_castSucc]
  rw [state_count_eq_sum_indicator]

omit [Fintype X] in
/-- State counts are invariant under coordinate permutations. -/
theorem state_count_smul (x : X) {N : ℕ} (σ : Equiv.Perm (Fin N))
    (f : Fin N → X) :
    (univ.filter (fun i : Fin N => f (σ.symm i) = x)).card =
      (univ.filter (fun i : Fin N => f i = x)).card := by
  rw [state_count_eq_card_subtype, state_count_eq_card_subtype]
  refine Fintype.card_congr ?_
  refine
    { toFun := fun i => ⟨σ.symm i.1, i.2⟩
      invFun := fun j => ⟨σ j.1, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · show f (σ.symm (σ j.1)) = x
    simpa using j.2
  · intro i
    ext
    simp
  · intro j
    ext
    simp

/-- Counts across all states add to the number of coordinates. -/
theorem sum_state_count {N : ℕ} (f : Fin N → X) :
    ∑ x : X, (univ.filter (fun i : Fin N => f i = x)).card = N := by
  calc
    ∑ x : X, (univ.filter (fun i : Fin N => f i = x)).card
        = ∑ x : X, ∑ i : Fin N, if f i = x then 1 else 0 := by
            refine Finset.sum_congr rfl ?_
            intro x _
            exact state_count_eq_sum_indicator x f
    _ = ∑ i : Fin N, ∑ x : X, if f i = x then 1 else 0 := by
            rw [Finset.sum_comm]
    _ = ∑ _i : Fin N, 1 := by
            refine Finset.sum_congr rfl ?_
            intro i _
            simp
    _ = N := by
            simp

omit [Fintype X] in
/-- Coordinate permutations preserve the whole pointwise count profile. -/
theorem countProfile_smul {N : ℕ} (σ : Equiv.Perm (Fin N)) (f : Fin N → X) :
    (fun x : X => (univ.filter (fun i : Fin N => f (σ.symm i) = x)).card) =
      fun x : X => (univ.filter (fun i : Fin N => f i = x)).card := by
  funext x
  exact state_count_smul x σ f

omit [Fintype X] in
/-- Membership in the finite permutation orbit expressed via `Finset.image`. -/
@[simp]
theorem mem_permutationOrbit_iff {N : ℕ} (f g : Fin N → X) :
    g ∈ (Finset.univ.image (fun σ : Equiv.Perm (Fin N) => fun i => f (σ.symm i))) ↔
      ∃ σ : Equiv.Perm (Fin N), (fun i => f (σ.symm i)) = g := by
  classical
  simp

/-- Membership in a finite macrostate fiber expressed via `Finset.filter`. -/
@[simp]
theorem mem_macrostateFiber_iff {N : ℕ} (p : X → ℕ) (g : Fin N → X) :
    g ∈ (Finset.univ.filter
      (fun h : Fin N → X => ∀ x : X, (univ.filter (fun i : Fin N => h i = x)).card = p x)) ↔
      ∀ x : X, (univ.filter (fun i : Fin N => g i = x)).card = p x := by
  classical
  simp

/-- The finite permutation orbit lies in the finite macrostate fiber. -/
theorem permutationOrbit_subset_macrostateFiber {N : ℕ} (f : Fin N → X) :
    (Finset.univ.image (fun σ : Equiv.Perm (Fin N) => fun i => f (σ.symm i))) ⊆
      Finset.univ.filter
        (fun g : Fin N → X => ∀ x : X,
          (univ.filter (fun i : Fin N => g i = x)).card =
            (univ.filter (fun i : Fin N => f i = x)).card) := by
  intro g hg
  rw [mem_permutationOrbit_iff] at hg
  rcases hg with ⟨σ, rfl⟩
  rw [mem_macrostateFiber_iff]
  intro x
  exact state_count_smul x σ f

/-- State counts are constant on the finite permutation orbit. -/
theorem state_count_eq_of_mem_permutationOrbit {N : ℕ} {f g : Fin N → X}
    (hg : g ∈ (Finset.univ.image (fun σ : Equiv.Perm (Fin N) => fun i => f (σ.symm i)))) :
    ∀ x : X,
      (univ.filter (fun i : Fin N => g i = x)).card =
        (univ.filter (fun i : Fin N => f i = x)).card := by
  have hg' := permutationOrbit_subset_macrostateFiber (X := X) f hg
  rw [mem_macrostateFiber_iff] at hg'
  exact hg'

omit [Fintype X] in
/-- A coordinate-deletion image has cardinality bounded by the original family. -/
theorem coordinateProjectionFootprint_card_le {N : ℕ} (k : Fin N)
    (S : Finset (Fin N → X)) :
    (S.image (fun f => fun i : {i : Fin N // i ≠ k} => f i.1)).card ≤ S.card := by
  classical
  exact Finset.card_image_le

omit [Fintype X] in
/-- Deleting the last coordinate cannot increase finite cardinality. -/
theorem tailProjectionFootprint_card_le {N : ℕ}
    (S : Finset (Fin (N + 1) → X)) :
    (S.image (fun f => fun i : Fin N => f (Fin.castSucc i))).card ≤ S.card := by
  classical
  exact Finset.card_image_le

/-- The multinomial macrostate expression is invariant under coordinate permutations. -/
theorem orbit_size_smul {N : ℕ} (σ : Equiv.Perm (Fin N)) (f : Fin N → X) :
    Nat.factorial N /
        ∏ x : X, Nat.factorial ((univ.filter (fun i : Fin N => f (σ.symm i) = x)).card) =
      Nat.factorial N /
        ∏ x : X, Nat.factorial ((univ.filter (fun i : Fin N => f i = x)).card) := by
  simp [state_count_smul]

omit [DecidableEq X] in
/-- Monotonicity of the secondary real ratio in the integer volume argument. -/
theorem secondary_normalization_mono {a b N : ℕ} (hab : a ≤ b) :
    (a : ℝ) / ((Fintype.card X : ℝ) ^ N) ≤
      (b : ℝ) / ((Fintype.card X : ℝ) ^ N) := by
  exact div_le_div_of_nonneg_right (by exact_mod_cast hab)
    (pow_nonneg (by exact_mod_cast (Nat.zero_le (Fintype.card X))) N)

/-- A maximal multinomial expression has maximal secondary-normalized ratio. -/
theorem orbit_size_dominance {N : ℕ} (f max_f : Fin N → X)
    (h_max : ∀ g : Fin N → X,
      Nat.factorial N / ∏ x : X, Nat.factorial ((univ.filter (fun i : Fin N => g i = x)).card) ≤
        Nat.factorial N / ∏ x : X, Nat.factorial ((univ.filter (fun i : Fin N => max_f i = x)).card)) :
    ((Nat.factorial N / ∏ x : X, Nat.factorial ((univ.filter (fun i : Fin N => f i = x)).card) : ℕ) : ℝ) /
        ((Fintype.card X : ℝ) ^ N) ≤
      ((Nat.factorial N / ∏ x : X, Nat.factorial ((univ.filter (fun i : Fin N => max_f i = x)).card) : ℕ) : ℝ) /
        ((Fintype.card X : ℝ) ^ N) := by
  exact secondary_normalization_mono (X := X) (h_max f)

end Gromov.Probability
