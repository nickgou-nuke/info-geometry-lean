import InfoGeometry.Algebra.FibonacciGrothendieckRing
import Mathlib.Data.Nat.Fib.Zeckendorf
import Mathlib

namespace InfoGeometry.Algebra.ZeckendorfBijection

/-!
# Zeckendorf Bijection — Bridging Mathlib's Zeckendorf with FibonacciGrothendieckRing

This file connects Mathlib's `Nat.zeckendorf` (Zeckendorf's theorem: every positive
integer has a unique representation as a sum of non-consecutive Fibonacci numbers)
with our `FibonacciGrothendieckRing` infrastructure based on the golden-ratio apex
`τ² = τ + 1`.

NO `sorry`, NO `axiom`, NO `admit`. Every line is kernel-checked.
-/

open Nat

/-- The Zeckendorf Fibonacci numbers: F₂ = 1, F₃ = 2, F₄ = 3, F₅ = 5, ...
Our convention uses indices k ≥ 0 corresponding to F_{k+2}. -/
def ZeckendorfFib (k : ℕ) : ℕ := fib (k + 2)

@[simp]
lemma ZeckendorfFib_zero : ZeckendorfFib 0 = 1 := by
  norm_num [ZeckendorfFib, fib_add_two]

@[simp]
lemma ZeckendorfFib_one : ZeckendorfFib 1 = 2 := by
  norm_num [ZeckendorfFib, fib_add_two]

@[simp]
lemma ZeckendorfFib_two : ZeckendorfFib 2 = 3 := by
  norm_num [ZeckendorfFib, fib_add_two]

/-- Convert Mathlib's Zeckendorf representation (indices ≥ 2) to our convention (indices ≥ 0). -/
def mathlibToOurRep (l : List ℕ) : List ℕ :=
  l.map (fun i => i - 2)

/-- Convert our Zeckendorf representation (indices ≥ 0) to Mathlib's convention (indices ≥ 2). -/
def ourToMathlibRep (l : List ℕ) : List ℕ :=
  l.map (fun k => k + 2)

/-- Our Zeckendorf representations are strictly decreasing lists with gaps ≥ 2. -/
def IsOurZeckendorfRep (l : List ℕ) : Prop :=
  l.Pairwise (fun a b => a ≥ b + 2)

lemma isChain_of_append_isChain {α : Type _} {R : α → α → Prop} {l : List α} {a : α}
    (h : List.IsChain R (l ++ [a])) : List.IsChain R l := by
  induction l with
  | nil => constructor
  | cons x l ih =>
    cases l with
    | nil => constructor
    | cons y l' =>
      have h_cons : List.IsChain R (x :: y :: (l' ++ [a])) := h
      rw [List.isChain_cons_cons] at h_cons
      rw [List.isChain_cons_cons]
      exact ⟨h_cons.1, ih h_cons.2⟩

lemma pairwise_of_chain {l : List ℕ} (h : List.IsChain (fun a b => a ≥ b + 2) l) :
    List.Pairwise (fun a b => a ≥ b + 2) l := by
  induction l with
  | nil => constructor
  | cons x l ih =>
    cases l with
    | nil => simp
    | cons y l' =>
      rw [List.isChain_cons_cons] at h
      have h_pairwise := ih h.2
      constructor
      · intro a' ha'
        simp only [List.mem_cons] at ha'
        cases ha' with
        | inl ha' =>
          subst ha'
          exact h.1
        | inr ha' =>
          have h_ya : y ≥ a' + 2 := List.rel_of_pairwise_cons h_pairwise ha'
          omega
      · exact h_pairwise

lemma pairwise_map_sub_two {l : List ℕ} (h_pairwise : List.Pairwise (fun a b => a ≥ b + 2) l)
    (h_ge : ∀ i ∈ l, i ≥ 2) :
    List.Pairwise (fun a b => a ≥ b + 2) (l.map (fun i => i - 2)) := by
  induction l with
  | nil => constructor
  | cons x l ih =>
    cases l with
    | nil => simp
    | cons y l' =>
      cases h_pairwise with
      | cons h₁ h₂ =>
        constructor
        · intro b hb
          simp only [List.mem_map] at hb
          rcases hb with ⟨c, hc_mem, hc_eq⟩
          subst hc_eq
          have h_xc : x ≥ c + 2 := List.rel_of_pairwise_cons (List.Pairwise.cons h₁ h₂) hc_mem
          have h_c_ge : c ≥ 2 := h_ge c (by simp [hc_mem])
          have h_x_ge : x ≥ 2 := h_ge x (by simp)
          dsimp only
          rw [Nat.sub_add_cancel h_c_ge]
          omega
        · apply ih h₂
          intro i hi
          apply h_ge i (by simp [hi])

lemma ge_two_of_zeckendorf_chain {l : List ℕ} (h : List.IsChain (fun a b => b + 2 ≤ a) (l ++ [0])) :
    ∀ j ∈ l, j ≥ 2 := by
  induction l with
  | nil =>
    intro j hj
    cases hj
  | cons x l ih =>
    intro j hj
    cases l with
    | nil =>
      simp only [List.mem_singleton] at hj
      subst hj
      change List.IsChain (fun a b => b + 2 ≤ a) [j, 0] at h
      rw [List.isChain_pair] at h
      exact h
    | cons y l' =>
      simp only [List.mem_cons] at hj
      have h_cons : List.IsChain (fun a b => b + 2 ≤ a) (x :: y :: (l' ++ [0])) := h
      rw [List.isChain_cons_cons] at h_cons
      cases hj with
      | inl hj =>
        subst hj
        have h_y_ge : y ≥ 2 := by
          apply ih h_cons.2 y
          simp
        omega
      | inr hj =>
        apply ih h_cons.2 j (by simp [hj])

/-- Round-trip: our → Mathlib → our gives identity. -/
theorem ourToMathlib_mathlibToOur (l : List ℕ) :
    mathlibToOurRep (ourToMathlibRep l) = l := by
  have h : (fun i => i - 2) ∘ (fun k => k + 2) = id := by
    funext x
    simp
  simp [mathlibToOurRep, ourToMathlibRep, List.map_map, h]

/-- Round-trip: Mathlib → our → Mathlib gives identity (when all elements ≥ 2). -/
theorem mathlibToOur_ourToMathlib {l : List ℕ} (h : ∀ i ∈ l, i ≥ 2) :
    ourToMathlibRep (mathlibToOurRep l) = l := by
  induction l with
  | nil => simp [mathlibToOurRep, ourToMathlibRep]
  | cons i l ih =>
    have h_i : i ≥ 2 := h i (by simp)
    have h_l : ∀ j ∈ l, j ≥ 2 := fun j hj => h j (by simp [hj])
    change (i - 2 + 2) :: ourToMathlibRep (mathlibToOurRep l) = i :: l
    rw [Nat.sub_add_cancel h_i, ih h_l]

/-- The sum of Fibonacci numbers is preserved under the representation conversion. -/
theorem sum_ourRep_eq_sum_mathlibRep {l : List ℕ} (h : ∀ i ∈ l, i ≥ 2) :
    ((mathlibToOurRep l).map ZeckendorfFib).sum = (l.map fib).sum := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    have h_i : i ≥ 2 := h i (by simp)
    have h_l : ∀ j ∈ l, j ≥ 2 := fun j hj => h j (by simp [hj])
    change fib (i - 2 + 2) + ((mathlibToOurRep l).map ZeckendorfFib).sum = fib i + (l.map fib).sum
    rw [ih h_l]
    have h_eq : fib (i - 2 + 2) = fib i := by
      have h₄ : i - 2 + 2 = i := by omega
      rw [h₄]
    rw [h_eq]

/-- The Zeckendorf representation of n using our index convention. -/
def ourZeckendorf (n : ℕ) : List ℕ := mathlibToOurRep n.zeckendorf

/-- The sum of our Zeckendorf Fibonacci numbers equals n. -/
theorem sum_ourZeckendorf (n : ℕ) : ((ourZeckendorf n).map ZeckendorfFib).sum = n := by
  rw [ourZeckendorf]
  have h₁ : (n.zeckendorf).IsZeckendorfRep := isZeckendorfRep_zeckendorf n
  simp only [List.IsZeckendorfRep] at h₁
  have h₂ : ∀ i ∈ n.zeckendorf, i ≥ 2 := ge_two_of_zeckendorf_chain h₁
  rw [sum_ourRep_eq_sum_mathlibRep h₂]
  rw [sum_zeckendorf_fib]

/-- The Zeckendorf representation from Mathlib satisfies our property. -/
theorem isOurZeckendorfRep_ourZeckendorf (n : ℕ) : IsOurZeckendorfRep (ourZeckendorf n) := by
  rw [ourZeckendorf]
  have h₁ : (n.zeckendorf).IsZeckendorfRep := isZeckendorfRep_zeckendorf n
  simp only [List.IsZeckendorfRep] at h₁
  have h₂ : ∀ i ∈ n.zeckendorf, i ≥ 2 := ge_two_of_zeckendorf_chain h₁
  have h_chain := isChain_of_append_isChain h₁
  have h_pairwise := pairwise_of_chain h_chain
  exact pairwise_map_sub_two h_pairwise h₂

end InfoGeometry.Algebra.ZeckendorfBijection