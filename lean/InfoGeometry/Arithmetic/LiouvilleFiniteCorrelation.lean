import InfoGeometry.Arithmetic.LiouvilleParity
import Mathlib.Data.Finset.Order

namespace InfoGeometry.Arithmetic.LiouvilleFiniteCorrelation

open scoped BigOperators
open BostConnesSystem

noncomputable def shiftedLiouville (index : ℕ+) (shift : ℕ) : ℤ :=
  liouville (index.val + shift)

inductive Archetype
  | factorization
  | multiplicativity
  | signValues
  | finiteCounting
  | finiteCorrelation
  | asymptoticCancellation
  deriving DecidableEq

def archetypeFinEquiv : Archetype ≃ Fin 6 where
  toFun
    | .factorization => 0
    | .multiplicativity => 1
    | .signValues => 2
    | .finiteCounting => 3
    | .finiteCorrelation => 4
    | .asymptoticCancellation => 5
  invFun i := match i.val with
    | 0 => .factorization
    | 1 => .multiplicativity
    | 2 => .signValues
    | 3 => .finiteCounting
    | 4 => .finiteCorrelation
    | _ => .asymptoticCancellation
  left_inv x := by cases x <;> rfl
  right_inv i := by
    apply Fin.ext
    fin_cases i <;> rfl

instance : Fintype Archetype := Fintype.ofEquiv (Fin 6) archetypeFinEquiv.symm

def prerequisites : Archetype → Finset ℕ
  | .factorization => {0}
  | .multiplicativity => {0, 1}
  | .signValues => {0, 2}
  | .finiteCounting => {3}
  | .finiteCorrelation => {0, 2, 3, 4}
  | .asymptoticCancellation => {0, 2, 3, 4, 5}

theorem prerequisites_injective : Function.Injective prerequisites := by decide

instance : PartialOrder Archetype :=
  PartialOrder.lift prerequisites prerequisites_injective

instance : DecidableRel (α := Archetype) (· ≤ ·) :=
  fun first second =>
    inferInstanceAs (Decidable (prerequisites first ⊆ prerequisites second))

instance : DecidableRel (fun first second : Archetype => first < second) := by
  intro first second
  change Decidable
    (prerequisites first ⊆ prerequisites second ∧
      ¬ prerequisites second ⊆ prerequisites first)
  infer_instance

theorem finite_correlation_dependencies :
    Archetype.signValues < Archetype.finiteCorrelation ∧
      Archetype.finiteCounting < Archetype.finiteCorrelation := by decide

theorem multiplicativity_and_counting_incomparable :
    ¬ Archetype.multiplicativity ≤ Archetype.finiteCounting ∧
      ¬ Archetype.finiteCounting ≤ Archetype.multiplicativity := by decide

theorem cancellation_is_additional_dependency :
    Archetype.finiteCorrelation < Archetype.asymptoticCancellation := by decide

theorem sign_product_eq_counting_term (first second : ℤ)
    (first_sq : first * first = 1) (second_sq : second * second = 1) :
    first * second = 2 * (if first = second then 1 else 0) - 1 := by
  rcases mul_self_eq_one_iff.mp first_sq with first_eq | first_eq <;>
    rcases mul_self_eq_one_iff.mp second_sq with second_eq | second_eq <;>
    simp [first_eq, second_eq]

theorem finite_sign_correlation {Index : Type*} (samples : Finset Index)
    (first second : Index → ℤ)
    (first_sq : ∀ index ∈ samples, first index * first index = 1)
    (second_sq : ∀ index ∈ samples, second index * second index = 1) :
    (∑ index ∈ samples, first index * second index) =
      2 * ((samples.filter (fun index => first index = second index)).card : ℤ) -
        (samples.card : ℤ) := by
  classical
  calc
    (∑ index ∈ samples, first index * second index) =
        ∑ index ∈ samples, (2 * (if first index = second index then 1 else 0) - 1) := by
      apply Finset.sum_congr rfl
      intro index member
      exact sign_product_eq_counting_term _ _
        (first_sq index member) (second_sq index member)
    _ = _ := by
      rw [Finset.sum_sub_distrib]
      have hcount :
          (∑ index ∈ samples, 2 * (if first index = second index then (1 : ℤ) else 0)) =
            2 * ((samples.filter (fun index => first index = second index)).card : ℤ) := by
        calc
          (∑ index ∈ samples, 2 * (if first index = second index then (1 : ℤ) else 0)) =
              2 * ∑ index ∈ samples, if first index = second index then (1 : ℤ) else 0 := by
            rw [← Finset.mul_sum]
          _ = _ := by rw [Finset.sum_boole]
      rw [hcount]
      simp

theorem liouville_correlation_count (samples : Finset ℕ+) (shift : ℕ) :
    (∑ index ∈ samples, liouville index * shiftedLiouville index shift) =
      2 * ((samples.filter (fun (index : ℕ+) =>
        liouville index = shiftedLiouville index shift)).card : ℤ) -
          (samples.card : ℤ) := by
  apply finite_sign_correlation (Index := ℕ+)
  · intro index member
    exact liouville_sq index index.pos
  · intro index member
    exact liouville_sq (index.val + shift)
      (by have positive := index.pos; omega)

theorem liouville_self_correlation (samples : Finset ℕ+) :
    (∑ index ∈ samples, liouville index * liouville index) =
      (samples.card : ℤ) := by
  calc
    (∑ index ∈ samples, liouville index * liouville index) =
        ∑ _index ∈ samples, (1 : ℤ) := by
      apply Finset.sum_congr rfl
      intro index member
      exact liouville_sq index index.pos
    _ = _ := by simp

theorem liouville_correlation_zero_iff (samples : Finset ℕ+) (shift : ℕ) :
    (∑ index ∈ samples, liouville index * shiftedLiouville index shift) = 0 ↔
      2 * ((samples.filter (fun (index : ℕ+) =>
        liouville index = shiftedLiouville index shift)).card : ℤ) =
          (samples.card : ℤ) := by
  rw [liouville_correlation_count, sub_eq_zero]

theorem liouville_correlation_abs_le (samples : Finset ℕ+) (shift : ℕ) :
    |∑ index ∈ samples, liouville index * shiftedLiouville index shift| ≤
      (samples.card : ℤ) := by
  have count_le := Finset.card_filter_le samples (fun (index : ℕ+) =>
    liouville index = shiftedLiouville index shift)
  rw [liouville_correlation_count]
  exact abs_le.mpr ⟨by omega, by omega⟩

theorem liouville_correlation_ne_zero_of_odd_card
    (samples : Finset ℕ+) (shift : ℕ) (odd_card : Odd samples.card) :
    (∑ index ∈ samples, liouville index * shiftedLiouville index shift) ≠ 0 := by
  intro zero_correlation
  have balance := (liouville_correlation_zero_iff samples shift).mp zero_correlation
  obtain ⟨half, cardinality⟩ := odd_card
  omega

end InfoGeometry.Arithmetic.LiouvilleFiniteCorrelation
