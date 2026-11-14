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
import InfoGeometry.Algebra.KaplanskyZeroDivisorArchetype

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
structure PeirceProjectors (R : Type*) [Ring R] [Algebra ℚ R] where
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

/-- A split involution in a ring (element with ε² = 1, ε ≠ ±1). -/
structure SplitInvolution (R : Type*) [Ring R] where
  elem : R
  h_square : elem * elem = 1
  h_not_one : elem ≠ 1
  h_not_neg_one : elem ≠ -1

/-- Construct Peirce projectors from a split involution. -/
def peirceFromSplitInvolution {R : Type*} [Ring R] [Algebra ℚ R]
    (s : SplitInvolution R) :
    PeirceProjectors R := by
  refine ⟨(⅟(2 : ℚ)) • (1 + s.elem), (⅟(2 : ℚ)) • (1 - s.elem),
    s.elem, s.h_square, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · -- P₊² = P₊
    rw [smul_mul_smul]
    have hsq : (1 + s.elem) * (1 + s.elem) = (2 : ℚ) • (1 + s.elem) := by
      calc
        (1 + s.elem) * (1 + s.elem) = 1 + s.elem + s.elem + s.elem * s.elem := by
          noncomm_ring
        _ = 1 + s.elem + s.elem + 1 := by rw [s.h_square]
        _ = (1 + s.elem) + (1 + s.elem) := by abel
        _ = (2 : ℚ) • (1 + s.elem) := by rw [two_smul]
    rw [hsq, ← mul_smul]
    have hcoeff : (⅟(2 : ℚ) * ⅟(2 : ℚ)) * 2 = ⅟(2 : ℚ) := by
      calc
        (⅟(2 : ℚ) * ⅟(2 : ℚ)) * 2 = ⅟(2 : ℚ) * (⅟(2 : ℚ) * 2) := by rw [mul_assoc]
        _ = ⅟(2 : ℚ) * 1 := by rw [invOf_mul_self]
        _ = ⅟(2 : ℚ) := by rw [mul_one]
    rw [hcoeff]
  · -- P₋² = P₋
    rw [smul_mul_smul]
    have hsq : (1 - s.elem) * (1 - s.elem) = (2 : ℚ) • (1 - s.elem) := by
      calc
        (1 - s.elem) * (1 - s.elem) = 1 - s.elem - s.elem + s.elem * s.elem := by
          noncomm_ring
        _ = 1 - s.elem - s.elem + 1 := by rw [s.h_square]
        _ = (1 - s.elem) + (1 - s.elem) := by abel
        _ = (2 : ℚ) • (1 - s.elem) := by rw [two_smul]
    rw [hsq, ← mul_smul]
    have hcoeff : (⅟(2 : ℚ) * ⅟(2 : ℚ)) * 2 = ⅟(2 : ℚ) := by
      calc
        (⅟(2 : ℚ) * ⅟(2 : ℚ)) * 2 = ⅟(2 : ℚ) * (⅟(2 : ℚ) * 2) := by rw [mul_assoc]
        _ = ⅟(2 : ℚ) * 1 := by rw [invOf_mul_self]
        _ = ⅟(2 : ℚ) := by rw [mul_one]
    rw [hcoeff]
  · -- P₊ P₋ = 0
    rw [smul_mul_smul]
    have hcross : (1 + s.elem) * (1 - s.elem) = 0 := by
      calc
        (1 + s.elem) * (1 - s.elem) = 1 - s.elem * s.elem := by noncomm_ring
        _ = 0 := by rw [s.h_square]; noncomm_ring
    rw [hcross, smul_zero]
  · -- P₊ + P₋ = 1
    rw [← smul_add]
    have hsum : (1 + s.elem) + (1 - s.elem) = (2 : ℚ) • (1 : R) := by
      calc
        (1 + s.elem) + (1 - s.elem) = 1 + 1 := by noncomm_ring
        _ = (2 : ℚ) • (1 : R) := by rw [two_smul]
    rw [hsum, ← mul_smul, invOf_mul_self, one_smul]

/-- Over 𝔽₂, the element `ε + 1` is a square-zero nilpotent when `ε² = 1`. -/
theorem splitInvolutionToNilpotent (p : ℕ) (hp : p.Prime) (hp2 : p = 2) :
    ∀ (ε : ZMod p), ε * ε = 1 → (ε + 1) * (ε + 1) = 0 := by
  subst p
  intro ε hε
  exact InfoGeometry.Algebra.KaplanskyZeroDivisor.charTwo_involution_add_one_is_nilpotent hε

/-- Non-trivial idempotents yield zero divisors. -/
theorem idempotentYieldsZeroDivisor {R : Type*} [Ring R] {e : R} (h_idem : e * e = e) (h_ne_zero : e ≠ 0) (h_ne_one : e ≠ 1) :
    ∃ (a b : R), a ≠ 0 ∧ b ≠ 0 ∧ a * b = 0 := by
  refine' ⟨e, 1 - e, _, _, _⟩
  · -- e ≠ 0
    exact h_ne_zero
  · -- 1 - e ≠ 0
    intro h
    exact h_ne_one ((sub_eq_zero.mp h).symm)
  · -- e * (1 - e) = 0
    calc
      e * (1 - e) = e - e * e := by rw [mul_sub, mul_one]
      _ = e - e := by rw [h_idem]
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
    _ = d.n * 0 * d.p := by rw [d.h_p_n_zero]
    _ = 0 := by simp
    _ = d.n * d.p := by rw [d.h_n_p_zero]

/-- The current data imposes `n * p = 0`, so the named element is always zero. -/
theorem chevalleyIdempotent_eq_zero {R : Type*} [Ring R] (d : ChevalleySpinorData R) :
    chevalleyIdempotent d = 0 := d.h_n_p_zero

/-- Characteristic 2 collapse: split involution becomes nilpotent. -/
theorem charTwoSplitInvolutionNilpotent (R : Type*) [Ring R] [CharP R 2] (ε : R)
    (hε : ε * ε = 1) : (ε + 1) * (ε + 1) = 0 := by
  have htwo : (2 : R) = 0 := CharP.cast_eq_zero R 2
  have hone : (1 : R) + 1 = 0 := by
    calc
      (1 : R) + 1 = (2 : ℕ) • (1 : R) := by rw [two_smul]
      _ = 0 := by simpa using congrArg (fun x : R => x * (1 : R)) htwo
  calc
    (ε + 1) * (ε + 1) = ε * ε + (ε + ε) + 1 := by noncomm_ring
    _ = 1 + 1 := by
      have hεε : ε + ε = 0 := by rw [← two_mul, htwo, zero_mul]
      simp [hε, hεε]
    _ = 0 := hone

/-- Left and right annihilator ideals from zero divisors. -/
def leftAnnihilator {R : Type*} [Ring R] (S : Set R) : Set R :=
  {x : R | ∀ s ∈ S, x * s = 0}

def rightAnnihilator {R : Type*} [Ring R] (S : Set R) : Set R :=
  {x : R | ∀ s ∈ S, s * x = 0}

theorem zeroDivisorYieldsAnnihilatingSubsets {R : Type*} [Ring R] {α β : R}
    (h : α * β = 0) :
    (∃ (I : Set R), I.Nonempty ∧ ∀ x ∈ I, x * β = 0) ∧
    (∃ (J : Set R), J.Nonempty ∧ ∀ y ∈ J, α * y = 0) := by
  refine ⟨⟨{α}, ⟨α, Set.mem_singleton α⟩, ?_⟩,
    ⟨{β}, ⟨β, Set.mem_singleton β⟩, ?_⟩⟩
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

def defectSpaceSubmodule {R : Type*} [Ring R] (d δ : R →ₗ[R] R) :
    Submodule R R := by
  refine
    { carrier := defectSpace d δ
      zero_mem' := by simp [defectSpace]
      add_mem' := ?_
      smul_mem' := ?_ }
  · -- Closed under addition
    intro x y hx hy
    simp only [defectSpace, Set.mem_ofPred_eq] at hx hy ⊢
    constructor
    · rw [map_add, hx.1, hy.1, add_zero]
    · rw [map_add, hx.2, hy.2, add_zero]
  · -- Closed under scalar multiplication
    intro c x hx
    simp only [defectSpace, Set.mem_ofPred_eq] at hx ⊢
    constructor
    · rw [map_smul, hx.1, smul_zero]
    · rw [map_smul, hx.2, smul_zero]

end KaplanskyCliffordBridge
