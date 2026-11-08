/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Projective.AttentionIdentifiability

/-!
# Minimum-ratio pruning in the existing homogeneous decoder

The step preserves the native linear map, not just one scalar coordinate.
A working set strictly decreases. Actual positive support strictly decreases
when the working set is the positive support. Iteration stops on native affine
independence, NOT merely when the number of keys reaches the ambient bound.
Classical finite minimum/dependence selection does not provide an executable
algorithm on arbitrary real inputs. The rational runtime is separate.
-/
noncomputable section
namespace InfoGeometry.Routing.CaratheodoryPivotContracts

open InfoGeometry.Projective.AttentionValueCoordinates
open InfoGeometry.Projective.AttentionIdentifiability
open scoped BigOperators

variable {J D : Type*} [Fintype J] [DecidableEq J]

lemma exists_positive_coordinate {δ : J → ℝ}
    (hm : ∑ j, δ j = 0) (hne : δ ≠ 0) : ∃ j, 0 < δ j := by
  by_contra! hn
  apply hne
  funext j
  have hs : ∑ i, -δ i = 0 := by simp [Finset.sum_neg_distrib, hm]
  have hz := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i (_ : i ∈ Finset.univ) => neg_nonneg.mpr (hn i))).mp hs j (Finset.mem_univ j)
  exact neg_eq_zero.mp hz

/-- Extend a native kernel vector on a dependent subtype by zero. -/
theorem dependent_support_kernel (V : J → D → ℝ) (S : Finset J)
    (hS : ¬ AffineIndependent ℝ (fun j : S => V j)) :
    ∃ δ : J → ℝ, δ ≠ 0 ∧ (∀ j ∉ S, δ j = 0) ∧
      δ ∈ (homogeneousDecoder V).ker := by
  classical
  obtain ⟨c, hc, hk⟩ := exists_nonzero_decoder_kernel (fun j : S => V j) hS
  let δ : J → ℝ := fun j => if hj : j ∈ S then c ⟨j, hj⟩ else 0
  have hs : ∀ j ∉ S, δ j = 0 := by intro j hj; simp [δ, hj]
  have he : homogeneousDecoder V δ = homogeneousDecoder (fun j : S => V j) c := by
    unfold homogeneousDecoder
    change (∑ j, δ j • affineLift (V j)) = ∑ j : S, c j • affineLift (V j)
    rw [← Finset.sum_subset (Finset.subset_univ S)
      (fun j _ hj => by rw [hs j hj, zero_smul])]
    rw [← Finset.sum_attach S]
    apply Finset.sum_congr rfl
    intro j _
    simp [δ, j.property]
  refine ⟨δ, ?_, hs, ?_⟩
  · intro h
    apply hc
    funext j
    have hh := congrFun h j
    simpa [δ, j.property] using hh
  · rw [LinearMap.mem_ker, he]
    exact LinearMap.mem_ker.mp hk

/-- One minimum-ratio step, with the actual pivot and all invariants. -/
theorem minimum_ratio_step (V : J → D → ℝ) (S : Finset J) (p δ : J → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hs : ∀ j ∉ S, p j = 0)
    (hδs : ∀ j ∉ S, δ j = 0) (hne : δ ≠ 0)
    (hk : δ ∈ (homogeneousDecoder V).ker) :
    ∃ j ∈ S, ∃ t : ℝ, ∃ q : J → ℝ,
      0 < δ j ∧ t = p j / δ j ∧ 0 ≤ t ∧
      (∀ i, 0 < δ i → t ≤ p i / δ i) ∧
      q = p - t • δ ∧ q j = 0 ∧
      (∀ i, 0 ≤ q i) ∧ (∀ i ∉ S.erase j, q i = 0) ∧
      (S.erase j).card < S.card ∧
      homogeneousDecoder V q = homogeneousDecoder V p ∧
      ((∀ i ∈ S, 0 < p i) → 0 < t) := by
  classical
  have hm := ((mem_ker_homogeneousDecoder_iff V δ).mp hk).1
  obtain ⟨j₀, hj₀⟩ := exists_positive_coordinate hm hne
  let T := Finset.univ.filter (fun j => 0 < δ j)
  have hT : T.Nonempty := ⟨j₀, by simp [T, hj₀]⟩
  obtain ⟨j, hj, hmin⟩ := Finset.exists_min_image T (fun i => p i / δ i) hT
  have hd : 0 < δ j := (Finset.mem_filter.mp hj).2
  have hjS : j ∈ S := by
    by_contra h
    exact (ne_of_gt hd) (hδs j h)
  let t := p j / δ j
  let q : J → ℝ := p - t • δ
  have ht : 0 ≤ t := div_nonneg (hp j) hd.le
  have hmin' (i : J) (hi : 0 < δ i) : t ≤ p i / δ i :=
    hmin i (by simp [T, hi])
  have hzero : q j = 0 := by
    change p j - (p j / δ j) * δ j = 0
    rw [div_mul_cancel₀ _ (ne_of_gt hd), sub_self]
  have hq (i : J) : 0 ≤ q i := by
    change 0 ≤ p i - t * δ i
    by_cases hi : 0 < δ i
    · exact sub_nonneg.mpr ((le_div_iff₀ hi).mp (hmin' i hi))
    · have hmul := mul_nonpos_of_nonneg_of_nonpos ht (le_of_not_gt hi)
      linarith [hp i]
  have hqs (i : J) (hi : i ∉ S.erase j) : q i = 0 := by
    by_cases hij : i = j
    · simpa [hij] using hzero
    · have hnot : i ∉ S := fun his => hi (Finset.mem_erase.mpr ⟨hij, his⟩)
      change p i - t * δ i = 0
      rw [hs i hnot, hδs i hnot, mul_zero, sub_self]
  refine ⟨j, hjS, t, q, hd, rfl, ht, hmin', rfl, hzero, hq, hqs, ?_, ?_, ?_⟩
  · have hc := Finset.card_erase_add_one hjS
    omega
  · change homogeneousDecoder V (p - t • δ) = _
    rw [map_sub, map_smul, LinearMap.mem_ker.mp hk, smul_zero, sub_zero]
  · intro hpos
    exact div_pos (hpos j hjS) hd

/-- Finite pivot induction terminates at an affinely independent working set. -/
theorem compression_by_support_induction (V : J → D → ℝ)
    (S : Finset J) (p : J → ℝ) (hp : ∀ j, 0 ≤ p j)
    (hs : ∀ j ∉ S, p j = 0) :
    ∃ T : Finset J, ∃ q : J → ℝ,
      T ⊆ S ∧ (∀ j, 0 ≤ q j) ∧ (∀ j ∉ T, q j = 0) ∧
      AffineIndependent ℝ (fun j : T => V j) ∧
      homogeneousDecoder V q = homogeneousDecoder V p := by
  classical
  suffices h : ∀ n : ℕ, ∀ S : Finset J, S.card = n → ∀ p : J → ℝ,
      (∀ j, 0 ≤ p j) → (∀ j ∉ S, p j = 0) →
      ∃ T : Finset J, ∃ q : J → ℝ,
        T ⊆ S ∧ (∀ j, 0 ≤ q j) ∧ (∀ j ∉ T, q j = 0) ∧
        AffineIndependent ℝ (fun j : T => V j) ∧
        homogeneousDecoder V q = homogeneousDecoder V p by
    exact h S.card S rfl p hp hs
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro S hn p hp hs
    by_cases hS : AffineIndependent ℝ (fun j : S => V j)
    · exact ⟨S, p, Finset.Subset.refl _, hp, hs, hS, rfl⟩
    · obtain ⟨δ, hne, hδs, hk⟩ := dependent_support_kernel V S hS
      obtain ⟨j, hj, t, q, _, _, _, _, _, _, hq, hqs, hcard, hval, _⟩ :=
        minimum_ratio_step V S p δ hp hs hδs hne hk
      obtain ⟨T, z, hT, hz, hzs, hTa, hzv⟩ :=
        ih (S.erase j).card (by omega) (S.erase j) rfl q hq hqs
      exact ⟨T, z, hT.trans (Finset.erase_subset _ _), hz, hzs, hTa, hzv.trans hval⟩

/-- Full simplex compression through finite pivots, using native affine independence. -/
theorem caratheodory_via_pivots [Fintype D]
    (V : J → D → ℝ) (S : Finset J) (p : J → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hm : ∑ j, p j = 1)
    (hs : ∀ j ∉ S, p j = 0) :
    ∃ T : Finset J, ∃ q : J → ℝ,
      T ⊆ S ∧ T.card ≤ Fintype.card D + 1 ∧
      (∀ j, 0 ≤ q j) ∧ (∑ j, q j) = 1 ∧ (∀ j ∉ T, q j = 0) ∧
      AffineIndependent ℝ (fun j : T => V j) ∧
      homogeneousDecoder V q = homogeneousDecoder V p := by
  obtain ⟨T, q, hT, hq, hqs, hTa, hval⟩ := compression_by_support_induction V S p hp hs
  have hcard := affineIndependent_card_le (fun j : T => V j) hTa
  have hmass := ((homogeneousDecoder_eq_iff V q p).mp hval).1
  exact ⟨T, q, hT, by simpa using hcard, hq, hmass.trans hm, hqs, hTa, hval⟩

end InfoGeometry.Routing.CaratheodoryPivotContracts
