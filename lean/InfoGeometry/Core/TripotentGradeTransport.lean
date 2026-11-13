/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.TripotentIntegerGrading
import Mathlib.Algebra.Ring.Action.ConjAct
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Transport and composite generators of the integer adjoint grading

Algebra equivalences transport the actual integer eigenspaces. An invertible
anticommuting conjugator reverses their degrees. Opposite-grade products lie
in the centralizer, without requiring either factor separately to commute.
These statements do not classify the whole normalizer of that centralizer.
-/

noncomputable section

namespace InfoGeometry.Core.TripotentAdjoint

open InfoGeometry.Physics.Algebra

variable {A B : Type*} [Ring A] [Algebra ℝ A] [Ring B] [Algebra ℝ B]

/-- Degree zero is the full centralizer, without requiring tripotence. -/
theorem mem_adGrade_zero_iff_commute (S X : A) :
    X ∈ adGrade S 0 ↔ Commute S X := by
  rw [mem_adGrade_iff]
  change S * X - X * S = (0 : ℝ) • X ↔ S * X = X * S
  rw [zero_smul, sub_eq_zero]

/-- Algebra equivalences transport integer eigenspaces with their generator. -/
theorem algEquiv_mem_adGrade_iff (f : A ≃ₐ[ℝ] B) (S X : A) (k : ℤ) :
    f X ∈ adGrade (f S) k ↔ X ∈ adGrade S k := by
  rw [mem_adGrade_iff, mem_adGrade_iff]
  have hmap : adOp (f S) (f X) = f (adOp S X) := by
    simp only [adOp, map_sub, map_mul]
  rw [hmap, ← map_smul]
  exact f.injective.eq_iff

/-- Negating the generator reverses each integer weight. -/
theorem mem_adGrade_neg_generator_iff (S X : A) (k : ℤ) :
    X ∈ adGrade (-S) k ↔ X ∈ adGrade S (-k) := by
  rw [mem_adGrade_iff, mem_adGrade_iff]
  have hneg : adOp (-S) X = -adOp S X := by
    unfold adOp
    noncomm_ring
  rw [hneg, neg_eq_iff_eq_neg]
  simp only [Int.cast_neg, neg_smul]

/-- A generator-reversing algebra automorphism gives an exact grade-reversal law. -/
theorem algEquiv_mem_adGrade_neg_iff (f : A ≃ₐ[ℝ] A) {S : A}
    (hS : f S = -S) (X : A) (k : ℤ) :
    f X ∈ adGrade S (-k) ↔ X ∈ adGrade S k := by
  have h := algEquiv_mem_adGrade_iff f S X k
  rw [hS, mem_adGrade_neg_generator_iff] at h
  exact h

/-- Conjugation by any anticommuting unit reverses the grades. No involution
assumption on the unit, and no tripotence assumption, is needed. -/
theorem unit_conjugate_mem_adGrade_neg_iff (W : Aˣ) {S : A}
    (hanti : (W : A) * S = -(S * (W : A))) (X : A) (k : ℤ) :
    (W : A) * X * (↑(W⁻¹) : A) ∈ adGrade S (-k) ↔ X ∈ adGrade S k := by
  let f : A ≃ₐ[ℝ] A :=
    MulSemiringAction.toAlgEquiv ℝ A (ConjAct.toConjAct W)
  have hf : f S = -S := by
    change (W : A) * S * (↑(W⁻¹) : A) = -S
    rw [hanti]
    simp only [neg_mul, mul_assoc, Units.mul_inv, mul_one]
  exact algEquiv_mem_adGrade_neg_iff f hf X k

/-- In particular, a reversing conjugation preserves the full centralizer. -/
theorem unit_conjugate_commute_iff (W : Aˣ) {S : A}
    (hanti : (W : A) * S = -(S * (W : A))) (X : A) :
    Commute S ((W : A) * X * (↑(W⁻¹) : A)) ↔ Commute S X := by
  simpa only [neg_zero, mem_adGrade_zero_iff_commute] using
    unit_conjugate_mem_adGrade_neg_iff W hanti X 0

/-- The actual product of opposite-degree operators is in the centralizer. -/
theorem commute_mul_of_opposite_adGrades {S J K : A} {k : ℤ}
    (hJ : J ∈ adGrade S k) (hK : K ∈ adGrade S (-k)) : Commute S (J * K) := by
  apply (mem_adGrade_zero_iff_commute S (J * K)).mp
  simpa only [add_neg_cancel] using mul_mem_adGrade_add hJ hK

/-- Finite sums of opposite-degree products remain centralizer elements. -/
theorem commute_sum_mul_of_opposite_adGrades {ι : Type*} (s : Finset ι)
    (d : ι → ℤ) (J K : ι → A) (S : A)
    (hJ : ∀ i ∈ s, J i ∈ adGrade S (d i))
    (hK : ∀ i ∈ s, K i ∈ adGrade S (-d i)) :
    Commute S (∑ i ∈ s, J i * K i) := by
  apply (mem_adGrade_zero_iff_commute S _).mp
  exact (adGrade S 0).sum_mem fun i hi =>
    (mem_adGrade_zero_iff_commute S _).mpr
      (commute_mul_of_opposite_adGrades (hJ i hi) (hK i hi))

/-- A finite sum of distinct homogeneous degrees commutes with its generator
exactly when every nonzero-degree component vanishes. -/
theorem commute_sum_adGrades_iff {S : A} (s : Finset ℤ) (X : ℤ → A)
    (hX : ∀ k ∈ s, X k ∈ adGrade S k) :
    Commute S (∑ k ∈ s, X k) ↔ ∀ k ∈ s, k ≠ 0 → X k = 0 := by
  constructor
  · intro hcomm k hk hk0
    have hsum : (∑ j ∈ s, (j : ℝ) • X j) = 0 := by
      calc
        _ = ∑ j ∈ s, adLinear S (X j) := by
          apply Finset.sum_congr rfl
          intro j hj
          exact (mem_adGrade_iff.mp (hX j hj)).symm
        _ = adLinear S (∑ j ∈ s, X j) := (map_sum (adLinear S) X s).symm
        _ = 0 := by
          change S * (∑ j ∈ s, X j) - (∑ j ∈ s, X j) * S = 0
          exact sub_eq_zero.mpr hcomm.eq
    have hcomponent :=
      (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero (adGrade S)).mp
        (adGrade_iSupIndep S) s (fun j : ℤ => (j : ℝ) • X j)
        (fun j hj => (adGrade S j).smul_mem (j : ℝ) (hX j hj)) hsum k hk
    exact (smul_eq_zero_iff_right
      (show (k : ℝ) ≠ 0 from Int.cast_ne_zero.mpr hk0)).mp hcomponent
  · intro hvan
    apply (mem_adGrade_zero_iff_commute S _).mp
    refine (adGrade S 0).sum_mem ?_
    intro k hk
    by_cases hk0 : k = 0
    · simpa only [hk0] using hX k hk
    · simpa only [hvan k hk hk0] using (adGrade S 0).zero_mem

/-- For an arbitrary finite homogeneous family, the centralizer condition
vanishes degree by degree after summing all terms of equal degree. -/
theorem commute_sum_iff_grouped_adGrades_eq_zero {ι : Type*} (s : Finset ι)
    (d : ι → ℤ) (X : ι → A) (S : A)
    (hX : ∀ i ∈ s, X i ∈ adGrade S (d i)) :
    Commute S (∑ i ∈ s, X i) ↔
      ∀ k : ℤ, k ≠ 0 → (∑ i ∈ s with d i = k, X i) = 0 := by
  classical
  let component : ℤ → A := fun k => ∑ i ∈ s with d i = k, X i
  have hcomponent (k : ℤ) : component k ∈ adGrade S k := by
    apply (adGrade S k).sum_mem
    intro i hi
    obtain ⟨his, hdegree⟩ := Finset.mem_filter.mp hi
    simpa only [hdegree] using hX i his
  have hrec : (∑ k ∈ s.image d, component k) = ∑ i ∈ s, X i :=
    Finset.sum_fiberwise_of_maps_to (s := s) (t := s.image d) (g := d)
      (fun i hi => Finset.mem_image_of_mem d hi) X
  have hgrouped :
      Commute S (∑ i ∈ s, X i) ↔
        ∀ k ∈ s.image d, k ≠ 0 → component k = 0 := by
    rw [← hrec]
    exact commute_sum_adGrades_iff (s.image d) component (fun k _ => hcomponent k)
  refine hgrouped.trans ?_
  constructor
  · intro h k hk0
    by_cases hk : k ∈ s.image d
    · exact h k hk hk0
    · apply Finset.sum_eq_zero
      intro i hi
      obtain ⟨his, hdegree⟩ := Finset.mem_filter.mp hi
      exact False.elim (hk (Finset.mem_image.mpr ⟨i, his, hdegree⟩))
  · intro h k _ hk0
    exact h k hk0

/-- Actual products of two finite homogeneous families commute in total
exactly when each nonzero total-degree fiber sums to zero. -/
theorem commute_sum_mul_iff_grouped_adGrades_eq_zero
    (s t : Finset ℤ) (J K : ℤ → A) (S : A)
    (hJ : ∀ m ∈ s, J m ∈ adGrade S m)
    (hK : ∀ n ∈ t, K n ∈ adGrade S n) :
    Commute S (∑ m ∈ s, ∑ n ∈ t, J m * K n) ↔
      ∀ k : ℤ, k ≠ 0 →
        (∑ p ∈ s.product t with p.1 + p.2 = k, J p.1 * K p.2) = 0 := by
  have hproduct (p : ℤ × ℤ) (hp : p ∈ s.product t) :
      J p.1 * K p.2 ∈ adGrade S (p.1 + p.2) :=
    mul_mem_adGrade_add (hJ p.1 (Finset.mem_product.mp hp).1)
      (hK p.2 (Finset.mem_product.mp hp).2)
  simpa only [Finset.sum_product] using
    commute_sum_iff_grouped_adGrades_eq_zero (s.product t)
      (fun p : ℤ × ℤ => p.1 + p.2) (fun p => J p.1 * K p.2) S hproduct

/-- Conjugation by a unit commuting with the generator preserves every grade,
with no tripotence or analytic-flow hypothesis. -/
theorem unit_conjugate_mem_adGrade_iff (U : Aˣ) {S : A}
    (hcomm : Commute (U : A) S) (X : A) (k : ℤ) :
    (U : A) * X * (↑(U⁻¹) : A) ∈ adGrade S k ↔ X ∈ adGrade S k := by
  let f : A ≃ₐ[ℝ] A :=
    MulSemiringAction.toAlgEquiv ℝ A (ConjAct.toConjAct U)
  have hf : f S = S := by
    change (U : A) * S * (↑(U⁻¹) : A) = S
    rw [hcomm.eq, mul_assoc, Units.mul_inv, mul_one]
  have h := algEquiv_mem_adGrade_iff f S X k
  rw [hf] at h
  exact h

/-- Such a conjugation preserves the centralizer in both directions. -/
theorem unit_conjugate_commute_iff_of_commute (U : Aˣ) {S : A}
    (hcomm : Commute (U : A) S) (X : A) :
    Commute S ((U : A) * X * (↑(U⁻¹) : A)) ↔ Commute S X := by
  simpa only [mem_adGrade_zero_iff_commute] using
    unit_conjugate_mem_adGrade_iff U hcomm X 0

end InfoGeometry.Core.TripotentAdjoint
