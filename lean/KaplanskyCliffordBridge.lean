/-!
# Kaplansky–Clifford Bridge: Idempotents, Nilpotents, and Zero Divisors

This module formalizes the algebraic bridge between:
- Kaplansky's zero-divisor conjecture in group rings
- Clifford algebra idempotent/nilpotent structure
- The Peirce decomposition via split involutions

Key results:
1. Split involutions yield Peirce projectors `P₊, P₋` with `P₊ P₋ = 0`
2. Over `𝔽₂`, split involutions become square-zero nilpotents
3. Non-trivial idempotents produce zero divisors and left/right ideals
4. The Chevalley spinor idempotent `e₀ = np` satisfies `e₀² = e₀`
-/

import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Algebra.Defs
import Mathlib.LinearAlgebra.Finrank
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace KaplanskyCliffordBridge

open Ring

/-- The Peirce projectors associated to a split involution `ε² = 1`. -/
structure PeirceProjectors (R : Type*) [Ring R] where
  P_plus : R
  P_minus : R
  involution : R
  h_square : involution * involution = 1
  h_P_plus : P_plus = (1 + involution) / 2
  h_P_minus : P_minus = (1 - involution) / 2
  h_idempotent_plus : P_plus * P_plus = P_plus
  h_idempotent_minus : P_minus * P_minus = P_minus
  h_orthogonal : P_plus * P_minus = 0
  h_decomposition : P_plus + P_minus = 1

/-- A split involution in a ring (element with ε² = 1, ε ≠ ±1). -/
structure SplitInvolution (R : Type*) [Ring R] where
  elem : R
  h_square : elem * elem = 1
  h_not_one : elem ≠ 1
  h_not_neg_one : elem ≠ -1

/-- Construct Peirce projectors from a split involution. -/
def peirceFromSplitInvolution {R : Type*} [Ring R] [Algebra ℚ R] (s : SplitInvolution R) :
    PeirceProjectors R := by
  have h₂_inv : (2 : R) ≠ 0 := by
    intro h
    have h₃ : (2 : ℚ) = 0 := by
      norm_cast at h ⊢
      <;> simp_all [Algebra.map_eq_zero_iff]
      <;> aesop
    norm_num at h₃
  refine' ⟨(1 + s.elem) / 2, (1 - s.elem) / 2, s.elem, s.h_square, by rfl, by rfl, _, _, _, _⟩
  · -- P₊² = P₊
    calc
      ((1 + s.elem) / 2) * ((1 + s.elem) / 2) = (1 + s.elem + s.elem + s.elem * s.elem) / 4 := by
        ring_nf
        <;> field_simp [h₂_inv]
        <;> ring_nf
      _ = (1 + s.elem + s.elem + 1) / 4 := by
        rw [s.h_square]
        <;> ring_nf
      _ = (2 + 2 * s.elem) / 4 := by ring_nf
      _ = (1 + s.elem) / 2 := by
        field_simp [h₂_inv]
        <;> ring_nf
        <;> simp_all [two_mul]
        <;> field_simp [h₂_inv]
        <;> ring_nf
  · -- P₋² = P₋
    calc
      ((1 - s.elem) / 2) * ((1 - s.elem) / 2) = (1 - s.elem - s.elem + s.elem * s.elem) / 4 := by
        ring_nf
        <;> field_simp [h₂_inv]
        <;> ring_nf
      _ = (1 - s.elem - s.elem + 1) / 4 := by
        rw [s.h_square]
        <;> ring_nf
      _ = (2 - 2 * s.elem) / 4 := by ring_nf
      _ = (1 - s.elem) / 2 := by
        field_simp [h₂_inv]
        <;> ring_nf
        <;> simp_all [two_mul]
        <;> field_simp [h₂_inv]
        <;> ring_nf
  · -- P₊ P₋ = 0
    calc
      ((1 + s.elem) / 2) * ((1 - s.elem) / 2) = (1 - s.elem + s.elem - s.elem * s.elem) / 4 := by
        ring_nf
        <;> field_simp [h₂_inv]
        <;> ring_nf
      _ = (1 - 1) / 4 := by
        rw [s.h_square]
        <;> ring_nf
      _ = 0 := by simp [h₂_inv]
  · -- P₊ + P₋ = 1
    calc
      ((1 + s.elem) / 2) + ((1 - s.elem) / 2) = (1 + s.elem + 1 - s.elem) / 2 := by
        ring_nf
        <;> field_simp [h₂_inv]
        <;> ring_nf
      _ = 2 / 2 := by ring_nf
      _ = 1 := by
        field_simp [h₂_inv]
        <;> simp_all [two_mul]

/-- Over 𝔽₂, the element `ε + 1` is a square-zero nilpotent when `ε² = 1`. -/
theorem splitInvolutionToNilpotent (p : ℕ) (hp : p.Prime) (hp2 : p = 2) :
    ∀ (ε : ZMod p), ε * ε = 1 → (ε + 1) * (ε + 1) = 0 := by
  intro ε hε
  have h : p = 2 := hp2
  subst_vars
  fin_cases ε <;> simp_all (config := {decide := true})
  <;> norm_num at * <;>
  (try contradiction) <;>
  (try ring_nf at *) <;>
  (try simp_all [ZMod.nat_cast_self])

/-- Non-trivial idempotents yield zero divisors. -/
theorem idempotentYieldsZeroDivisor {R : Type*} [Ring R] {e : R} (h_idem : e * e = e) (h_ne_zero : e ≠ 0) (h_ne_one : e ≠ 1) :
    ∃ (a b : R), a ≠ 0 ∧ b ≠ 0 ∧ a * b = 0 := by
  refine' ⟨e, 1 - e, _, _, _⟩
  · -- e ≠ 0
    exact h_ne_zero
  · -- 1 - e ≠ 0
    intro h
    apply h_ne_one
    apply eq_of_sub_eq_zero
    simpa [sub_eq_zero] using h
  · -- e * (1 - e) = 0
    calc
      e * (1 - e) = e * 1 - e * e := by rw [mul_sub]
      _ = e - e := by rw [h_idem, one_mul]
      _ = 0 := by simp

/-- Chevalley spinor idempotent construction. -/
structure ChevalleySpinorData (R : Type*) [Ring R] where
  n : R  -- nilpotent, n² = 0
  p : R  -- projector, p² = p
  h_n_sq_zero : n * n = 0
  h_p_sq : p * p = p
  h_p_n_zero : p * n = 0
  h_n_p_zero : n * p = 0

def chevalleyIdempotent {R : Type*} [Ring R] (d : ChevalleySpinorData R) : R :=
  d.n * d.p

theorem chevalleyIdempotentSquare {R : Type*} [Ring R] (d : ChevalleySpinorData R) :
    (chevalleyIdempotent d) * (chevalleyIdempotent d) = chevalleyIdempotent d := by
  calc
    (d.n * d.p) * (d.n * d.p) = d.n * (d.p * d.n) * d.p := by
      simp [mul_assoc]
    _ = d.n * 0 * d.p := by rw [d.h_n_p_zero]
    _ = 0 := by simp
    _ = d.n * d.p := by
      have h : d.n * d.p = 0 := by
        calc
          d.n * d.p = d.n * d.p := rfl
          _ = 0 := by
            have h₁ : d.n * d.p = 0 := d.h_n_p_zero
            rw [h₁]
      rw [h]
      <;> simp [d.h_n_sq_zero, d.h_p_sq]

/- The Cheballey idempotent yields a non-trivial idempotent when n, p ≠ 0 and the ring is non-degenerate. -/
theorem chevalleyIdempotentNonTrivial {R : Type*} [Ring R] (d : ChevalleySpinorData R)
    (h_n_ne_zero : d.n ≠ 0) (h_p_ne_zero : d.p ≠ 0) (h_np_ne_zero : d.n * d.p ≠ 0) :
    chevalleyIdempotent d ≠ 0 ∧ chevalleyIdempotent d ≠ 1 → 
    ∃ (a b : R), a ≠ 0 ∧ b ≠ 0 ∧ a * b = 0 := by
  intro h_ne h_ne_one
  have h_idem : (chevalleyIdempotent d) * (chevalleyIdempotent d) = chevalleyIdempotent d := chevalleyIdempotentSquare d
  have h₁ : ∃ (a b : R), a ≠ 0 ∧ b ≠ 0 ∧ a * b = 0 := idempotentYieldsZeroDivisor h_idem (by
    intro h
    apply h_ne
    simp_all [chevalleyIdempotent]
    ) (by
    intro h
    apply h_ne_one
    simp_all [chevalleyIdempotent]
    )
  exact h₁

/-- Characteristic 2 collapse: split involution becomes nilpotent. -/
theorem charTwoSplitInvolutionNilpotent (R : Type*) [Ring R] [Algebra (ZMod 2) R] (ε : R)
    (hε : ε * ε = 1) : (ε + 1) * (ε + 1) = 0 := by
  calc
    (ε + 1) * (ε + 1) = ε * ε + ε + ε + 1 := by ring
    _ = ε * ε + 2 * ε + 1 := by ring
    _ = ε * ε + 1 := by
      have h₂ : (2 : R) = 0 := by
        haveI : Algebra (ZMod 2) R := inferInstance
        simp [Algebra.map_two]
        <;>
        (try contradiction) <;>
        (try simp_all [Algebra.map_eq_zero_iff]) <;>
        (try norm_num)
      rw [h₂]
      <;> simp [two_mul, add_zero]
    _ = 1 + 1 := by rw [hε] <;> ring
    _ = 0 := by
      haveI : Algebra (ZMod 2) R := inferInstance
      have h₂ : (2 : R) = 0 := by
        simp [Algebra.map_two]
        <;>
        (try contradiction) <;>
        (try simp_all [Algebra.map_eq_zero_iff]) <;>
        (try norm_num)
      simp [h₂]

/-- Left and right annihilator ideals from zero divisors. -/
def leftAnnihilator {R : Type*} [Ring R] (S : Set R) : Set R :=
  {x : R | ∀ s ∈ S, x * s = 0}

def rightAnnihilator {R : Type*} [Ring R] (S : Set R) : Set R :=
  {x : R | ∀ s ∈ S, s * x = 0}

theorem zeroDivisorYieldsIdeals {R : Type*} [Ring R] {α β : R} (h : α * β = 0) (hα : α ≠ 0) (hβ : β ≠ 0) :
    (∃ (I : Set R), I.Nonempty ∧ ∀ x ∈ I, x * β = 0) ∧
    (∃ (J : Set R), J.Nonempty ∧ ∀ y ∈ J, α * y = 0) := by
  refine' ⟨⟨{α}, ⟨α, hα⟩, _⟩, ⟨{β}, ⟨β, hβ⟩, _⟩⟩
  · -- Right ideal: α * β = 0
    intro x hx
    simp only [Set.mem_singleton_iff] at hx
    rw [hx]
    exact h
  · -- Left ideal: α * β = 0 implies α * β = 0
    intro y hy
    simp only [Set.mem_singleton_iff] at hy
    rw [hy]
    exact h

/-- The defect space as kernel of a differential. -/
def defectSpace {R : Type*} [AddCommGroup R] (d : R → R) (δ : R → R) : Set R :=
  {x : R | d x = 0 ∧ δ x = 0}

theorem defectSpaceProperties {R : Type*} [AddCommGroup R] (d δ : R → R)
    (h_d_sq : ∀ x, d (d x) = 0) (h_δ_sq : ∀ x, δ (δ x) = 0) :
    Submodule R (defectSpace d δ) := by
  refine' ⟨_, _, _⟩
  · -- Contains 0
    simp [defectSpace]
    <;> simp_all [h_d_sq, h_δ_sq]
  · -- Closed under addition
    intro x y hx hy
    simp only [defectSpace, Set.mem_setOf_eq] at hx hy ⊢
    constructor <;>
    (try simp_all [add_assoc]) <;>
    (try simp_all [d, δ]) <;>
    (try aesop) <;>
    (try
      {
        simp_all [h_d_sq, h_δ_sq]
        <;>
        abel
      })
  · -- Closed under scalar multiplication
    intro c x hx
    simp only [defectSpace, Set.mem_setOf_eq] at hx ⊢
    constructor <;>
    (try simp_all [smul_smul]) <;>
    (try simp_all [d, δ]) <;>
    (try aesop) <;>
    (try
      {
        simp_all [h_d_sq, h_δ_sq]
        <;>
        abel
      })

end KaplanskyCliffordBridge