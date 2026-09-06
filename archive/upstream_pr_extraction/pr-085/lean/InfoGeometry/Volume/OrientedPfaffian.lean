import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

noncomputable section

namespace InfoGeometry.Volume.OrientedPfaffian

open scoped BigOperators

structure PerfectMatching (m : ℕ) where
  partner : Fin (2 * m) → Fin (2 * m)
  involutive : Function.Involutive partner
  fixed_free : ∀ i, partner i ≠ i

noncomputable instance perfectMatchingFintype (m : ℕ) : Fintype (PerfectMatching m) :=
  Fintype.ofInjective (fun M : PerfectMatching m => M.partner) (by
    intro M N h
    cases M with
    | mk f hf hff =>
      cases N with
      | mk g hg hgf => simp_all)

namespace PerfectMatching

variable {m : ℕ}

@[simp] theorem partner_partner (M : PerfectMatching m) (i : Fin (2 * m)) :
    M.partner (M.partner i) = i := M.involutive i

@[simp] theorem partner_ne_self (M : PerfectMatching m) (i : Fin (2 * m)) :
    M.partner i ≠ i := M.fixed_free i

theorem partner_injective (M : PerfectMatching m) : Function.Injective M.partner :=
  M.involutive.injective

theorem partner_surjective (M : PerfectMatching m) : Function.Surjective M.partner :=
  M.involutive.surjective

def leftEndpoints (M : PerfectMatching m) : Finset (Fin (2 * m)) :=
  Finset.univ.filter fun i => i < M.partner i

def rightEndpoints (M : PerfectMatching m) : Finset (Fin (2 * m)) :=
  Finset.univ.filter fun i => M.partner i < i

@[simp] theorem mem_leftEndpoints (M : PerfectMatching m) (i : Fin (2 * m)) :
    i ∈ M.leftEndpoints ↔ i < M.partner i := by simp [leftEndpoints]

@[simp] theorem mem_rightEndpoints (M : PerfectMatching m) (i : Fin (2 * m)) :
    i ∈ M.rightEndpoints ↔ M.partner i < i := by simp [rightEndpoints]

theorem leftEndpoints_union_rightEndpoints (M : PerfectMatching m) :
    M.leftEndpoints ∪ M.rightEndpoints = Finset.univ := by
  ext i
  simp only [Finset.mem_union, mem_leftEndpoints, mem_rightEndpoints,
    Finset.mem_univ, iff_true]
  exact lt_or_gt_of_ne (Ne.symm (M.partner_ne_self i))

theorem leftEndpoints_disjoint_rightEndpoints (M : PerfectMatching m) :
    Disjoint M.leftEndpoints M.rightEndpoints := by
  refine Finset.disjoint_left.2 ?_
  intro i hi hj
  rw [M.mem_leftEndpoints] at hi
  rw [M.mem_rightEndpoints] at hj
  exact (lt_asymm hi hj)

theorem leftEndpoints_card_eq_rightEndpoints_card (M : PerfectMatching m) :
    M.leftEndpoints.card = M.rightEndpoints.card := by
  refine Finset.card_bij (fun i _ => M.partner i) ?_ ?_ ?_
  · intro i hi
    rw [M.mem_leftEndpoints] at hi
    rw [M.mem_rightEndpoints]
    simpa using hi
  · intro i₁ h₁ i₂ h₂ h
    exact M.partner_injective h
  · intro j hj
    refine ⟨M.partner j, ?_, M.partner_partner j⟩
    rw [M.mem_rightEndpoints] at hj
    rw [M.mem_leftEndpoints]
    simpa using hj

theorem leftEndpoints_card_add_rightEndpoints_card (M : PerfectMatching m) :
    M.leftEndpoints.card + M.rightEndpoints.card = 2 * m := by
  have h := Finset.card_union_of_disjoint (M.leftEndpoints_disjoint_rightEndpoints)
  rw [M.leftEndpoints_union_rightEndpoints] at h
  simpa using h.symm

theorem leftEndpoints_card (M : PerfectMatching m) : M.leftEndpoints.card = m := by
  have hsum := M.leftEndpoints_card_add_rightEndpoints_card
  have heq := M.leftEndpoints_card_eq_rightEndpoints_card
  omega

def matchingWeight
    (A : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ)
    (M : PerfectMatching m) : ℝ :=
  ∏ i ∈ M.leftEndpoints, A i (M.partner i)

def crossingPairs (M : PerfectMatching m) :
    Finset (Fin (2 * m) × Fin (2 * m)) :=
  (M.leftEndpoints.product M.leftEndpoints).filter fun p =>
    p.1 < p.2 ∧ p.2 < M.partner p.1 ∧ M.partner p.1 < M.partner p.2

def crossingNumber (M : PerfectMatching m) : ℕ := M.crossingPairs.card

def matchingSign (M : PerfectMatching m) : ℝ := (-1 : ℝ) ^ M.crossingNumber

@[simp] theorem matchingSign_sq (M : PerfectMatching m) :
    M.matchingSign ^ 2 = 1 := by
  simp [matchingSign, ← pow_mul]

end PerfectMatching

def orientedPfaffian (m : ℕ)
    (A : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ) : ℝ :=
  ∑ M : PerfectMatching m, M.matchingSign * M.matchingWeight A

/-- The canonical two-point matching. -/
def twoPointMatching : PerfectMatching 1 where
  partner := ![1, 0]
  involutive := by intro i; fin_cases i <;> rfl
  fixed_free := by intro i; fin_cases i <;> decide

theorem twoPointMatching_unique (M : PerfectMatching 1) :
    M = twoPointMatching := by
  cases M with
  | mk p hp hfree =>
    congr
    funext i
    fin_cases i
    · have h := hfree 0
      apply Fin.ext
      change (p 0).val = 1
      have hval : (p 0).val ≠ 0 := by
        intro hz
        apply h
        exact Fin.ext hz
      omega
    · have h := hfree 1
      apply Fin.ext
      change (p 1).val = 0
      have hval : (p 1).val ≠ 1 := by
        intro hz
        apply h
        exact Fin.ext hz
      omega

theorem orientedPfaffian_fin_two (a : ℝ) :
    orientedPfaffian 1 (!![(0 : ℝ), a; -a, 0]) = a := by
  classical
  letI : Unique (PerfectMatching 1) :=
    { default := twoPointMatching
      uniq := twoPointMatching_unique }
  change (∑ M : PerfectMatching 1,
    M.matchingSign * M.matchingWeight (!![(0 : ℝ), a; -a, 0])) = a
  rw [Fintype.sum_unique]
  change twoPointMatching.matchingSign *
      twoPointMatching.matchingWeight (!![(0 : ℝ), a; -a, 0]) = a
  have hleft : twoPointMatching.leftEndpoints = ({0} : Finset (Fin 2)) := by
    ext i
    fin_cases i <;> simp [twoPointMatching, PerfectMatching.leftEndpoints]
  have hcross : twoPointMatching.crossingPairs = ∅ := by
    ext p
    rcases p with ⟨i, j⟩
    fin_cases i <;> fin_cases j <;>
      simp [twoPointMatching, PerfectMatching.crossingPairs,
        PerfectMatching.leftEndpoints]
  have hsign : twoPointMatching.matchingSign = 1 := by
    simp [PerfectMatching.matchingSign, PerfectMatching.crossingNumber, hcross]
  have hweight : twoPointMatching.matchingWeight
      (!![(0 : ℝ), a; -a, 0]) = a := by
    unfold PerfectMatching.matchingWeight
    rw [hleft]
    simp [twoPointMatching]
  rw [hsign, hweight]
  norm_num

@[simp] theorem orientedPfaffian_eq_matchingSum (m : ℕ)
    (A : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ) :
    orientedPfaffian m A =
      ∑ M : PerfectMatching m, M.matchingSign * M.matchingWeight A := rfl

def IsSkew {m : ℕ}
    (A : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ) : Prop :=
  ∀ i j, A i j = -A j i

theorem IsSkew.diagonal_zero {m : ℕ}
    {A : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ}
    (hA : IsSkew A) (i : Fin (2 * m)) : A i i = 0 := by
  have h := hA i i
  linarith

end InfoGeometry.Volume.OrientedPfaffian
