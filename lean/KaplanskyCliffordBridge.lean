/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Algebra.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

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

namespace KaplanskyCliffordBridge

open Ring

/-- The Peirce projectors associated to a split involution `ε² = 1`. -/
structure PeirceProjectors (R : Type*) [Field R] where
  P_plus : R
  P_minus : R
  involution : R
  h_square : involution * involution = 1
  h_P_plus : P_plus = (⅟(2 : ℚ)) • (1 + involution)
  h_P_minus : P_minus = (⅟(2 : ℚ)) • (1 - involution)
  h_idempotent_plus : P_plus * P_plus = P_plus
  h_idempotent_minus : P_minus * P_minus = P_minus
  h_orthogonal : P_plus * P_minus = 0
  h_decomposition : P_plus + P_minus = 1

/-- Construct Peirce projectors from a split involution. -/
def peirceFromSplitInvolution {R : Type*} [Field R] [CharZero R]
    (ε : R) (hε : ε * ε = 1) :
    PeirceProjectors R := by
  have h₂_inv : (2 : R) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (by norm_num)
  have h_square_pow : ε ^ 2 = 1 := by
    simpa [pow_two] using hε
  refine ⟨(1 + ε) / (2 : R), (1 - ε) / (2 : R), ε,
    hε,
    (by rw [invOf_eq_inv, Rat.smul_def, Rat.cast_inv, Rat.cast_ofNat]; ring),
    (by rw [invOf_eq_inv, Rat.smul_def, Rat.cast_inv, Rat.cast_ofNat]; ring),
    ?_, ?_, ?_, ?_⟩
  · field_simp [h₂_inv]
    ring_nf
    rw [h_square_pow]
    ring
  · field_simp [h₂_inv]
    ring_nf
    rw [h_square_pow]
    ring
  · field_simp [h₂_inv]
    ring_nf
    rw [h_square_pow]
    ring
  · field_simp [h₂_inv]
    ring

/-- Non-trivial idempotents yield zero divisors. -/
theorem idempotentYieldsZeroDivisor {R : Type*} [Ring R] {e : R} (h_idem : e * e = e) (h_ne_zero : e ≠ 0) (h_ne_one : e ≠ 1) :
    ∃ (a b : R), a ≠ 0 ∧ b ≠ 0 ∧ a * b = 0 := by
  refine' ⟨e, 1 - e, _, _, _⟩
  · -- e ≠ 0
    exact h_ne_zero
  · -- 1 - e ≠ 0
    intro h
    apply h_ne_one
    exact (sub_eq_zero.mp h).symm
  · -- e * (1 - e) = 0
    calc
      e * (1 - e) = e * 1 - e * e := by rw [mul_sub]
      _ = e - e := by rw [h_idem, mul_one]
      _ = 0 := by simp

/-- Product of two algebra elements, used as a candidate factorized idempotent. -/
def chevalleyIdempotent {R : Type*} [Ring R] (n p : R) : R := n * p

theorem chevalleyIdempotentSquare {R : Type*} [Ring R] (n p : R)
    (hn : n * n = 0) (hp : p * p = 0) (hpn : p * n = 1 - n * p) :
    chevalleyIdempotent n p * chevalleyIdempotent n p = chevalleyIdempotent n p := by
  calc
    (n * p) * (n * p) = n * (p * n) * p := by noncomm_ring
    _ = n * (1 - n * p) * p := by rw [hpn]
    _ = n * p - (n * n) * (p * p) := by noncomm_ring
    _ = n * p := by simp [hn, hp]

/-- A nontrivial instance of the constructed idempotent gives zero divisors. -/
theorem chevalleyIdempotentNonTrivial {R : Type*} [Ring R] (n p : R)
    (hn : n * n = 0) (hp : p * p = 0) (hpn : p * n = 1 - n * p)
    (h_np_ne_zero : n * p ≠ 0) (h_ne_one : chevalleyIdempotent n p ≠ 1) :
    ∃ (a b : R), a ≠ 0 ∧ b ≠ 0 ∧ a * b = 0 := by
  have h_idem : chevalleyIdempotent n p * chevalleyIdempotent n p = chevalleyIdempotent n p :=
    chevalleyIdempotentSquare n p hn hp hpn
  exact idempotentYieldsZeroDivisor h_idem h_np_ne_zero h_ne_one

/-- Characteristic 2 collapse: split involution becomes nilpotent. -/
theorem charTwoSplitInvolutionNilpotent (R : Type*) [Ring R] (h₂ : (2 : R) = 0) (ε : R)
    (hε : ε * ε = 1) : (ε + 1) * (ε + 1) = 0 := by
  have htwo : (2 : R) = 0 := h₂
  have hone : (1 : R) + 1 = 0 := by
    calc
      (1 : R) + 1 = (2 : ℕ) • (1 : R) := by rw [two_smul]
      _ = 0 := by simpa using congrArg (fun x : R => x * (1 : R)) htwo
  calc
    (ε + 1) * (ε + 1) = ε * ε + 2 * ε + 1 := by noncomm_ring
    _ = 1 + 1 := by rw [hε, h₂]; simp
    _ = (2 : R) := by norm_num
    _ = 0 := h₂

/-- Left and right annihilators of a subset. -/
def leftAnnihilator {R : Type*} [Ring R] (S : Set R) : Set R :=
  {x : R | ∀ s ∈ S, x * s = 0}

def rightAnnihilator {R : Type*} [Ring R] (S : Set R) : Set R :=
  {x : R | ∀ s ∈ S, s * x = 0}

/-- A nonzero zero-divisor pair witnesses nonzero elements in the corresponding
left and right annihilators. -/
theorem zeroDivisorYieldsAnnihilators {R : Type*} [Ring R] {α β : R}
    (h : α * β = 0) (hα : α ≠ 0) (hβ : β ≠ 0) :
    (∃ x, x ∈ leftAnnihilator {β} ∧ x ≠ 0) ∧
    (∃ y, y ∈ rightAnnihilator {α} ∧ y ≠ 0) := by
  refine ⟨⟨α, ?_, hα⟩, ⟨β, ?_, hβ⟩⟩
  · intro s hs
    have : s = β := Set.mem_singleton_iff.mp hs
    simpa [this] using h
  · intro s hs
    have : s = α := Set.mem_singleton_iff.mp hs
    simpa [this] using h

/-- The common kernel of two linear operators. -/
def defectSpace {R : Type*} [Semiring R] [Module R R] (d δ : R →ₗ[R] R) : Submodule R R :=
  LinearMap.ker d ⊓ LinearMap.ker δ

theorem defectSpaceProperties {R : Type*} [Semiring R] [Module R R]
    (d δ : R →ₗ[R] R) :
    ∀ x : R, x ∈ defectSpace d δ ↔ d x = 0 ∧ δ x = 0 := by
  intro x
  rfl

end KaplanskyCliffordBridge
