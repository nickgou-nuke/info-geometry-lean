/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import InfoGeometry.Algebra.CyclotomicQuadraticBooleanSignBridge

/-!
# InfoGeometry.Arithmetic.TateAdelicSignAndOddCharacterCosetBridge

Constructive Lean 4 formalization of the two adelic / chiral sign fixes from
Tate's thesis (Track B.1 & B.2):

1. **Tate's Opposite-Sign Global Adelic Character Triviality on `ℚ`:**
   - `same_sign_character_fails_at_one_third`: using the same sign at `ℝ` and
     `ℚ₃` fails on `1/3 ∈ ℚ` (`exp(2πi/3) * exp(2πi/3) ≠ 1`).
   - `tate_opposite_sign_character_trivial_on_rat`: using opposite signs
     (`exp(-2πi q)` at `∞` vs `∏ exp(2πi frac_p)` at finite primes) gives exact
     triviality `= 1` for every `q ∈ ℚ` whenever `q - ∑ frac_p ∈ ℤ`.
2. **Odd-Character Erasure by Even Subgroup Indicators vs. Shifted Cosets:**
   - `odd_char_sum_even_test_eq_zero`: for any odd character `χ : (ZMod m)ˣ →* ℂ`
     (`χ (-1) = -1`) and any even test function `f (-u) = f u` (such as any
     origin-centered subgroup indicator `1_{K_v}`), `∑ u, χ u * f u = 0`.
   - `odd_char_shifted_coset_eq_one`: the shifted coset indicator `1_{1}` (the
     finite-level shadow of `1_{1 + pℤ_p}`) evaluates to `1 ≠ 0`.
   - `odd_quad_char_mod3_witness`: concrete witness via `primeQuadCharHom 3`
     (`CyclotomicQuadraticBooleanSignBridge`), proving `primeQuadCharHom 3 (-1) = -1`.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.TateAdelicSignAndOddCharacterCosetBridge

open scoped BigOperators
open InfoGeometry.Algebra.CyclotomicQuadraticBooleanSignBridge

/-! ## 1. Tate's opposite-sign global adelic character on `ℚ` -/

/-- Standard positive-sign additive circle character `e(x) = exp(2π i x)`. -/
def addCharPos (x : ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))

/-- Standard negative-sign (Archimedean) additive circle character `e(-x) = exp(-2π i x)`. -/
def addCharNeg (x : ℝ) : ℂ :=
  Complex.exp (-(2 * Real.pi * Complex.I * (x : ℂ)))

theorem addCharPos_add (x y : ℝ) :
    addCharPos (x + y) = addCharPos x * addCharPos y := by
  unfold addCharPos
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem addCharPos_int (n : ℤ) :
    addCharPos (n : ℝ) = 1 := by
  unfold addCharPos
  have h : 2 * (Real.pi : ℂ) * Complex.I * ((n : ℝ) : ℂ) =
      (n : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [h]
  exact Complex.exp_int_mul_two_pi_mul_I n

theorem addCharNeg_mul_addCharPos (x y : ℝ) :
    addCharNeg x * addCharPos y = addCharPos (y - x) := by
  unfold addCharNeg addCharPos
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem addCharPos_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    (∏ i ∈ s, addCharPos (f i)) = addCharPos (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp [addCharPos]
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, addCharPos_add]

/-- **Refutation of same-sign adelic character on `1/3 ∈ ℚ`**:
`exp(2π i / 3) * exp(2π i / 3) = exp(4π i / 3) ≠ 1`. -/
theorem same_sign_character_fails_at_one_third :
    addCharPos (1 / 3 : ℝ) * addCharPos (1 / 3 : ℝ) ≠ 1 := by
  rw [← addCharPos_add]
  unfold addCharPos
  intro h
  have hre : (Complex.exp (2 * Real.pi * Complex.I * ((1 / 3 + 1 / 3 : ℝ) : ℂ))).re = 1 := by
    rw [h]
    simp
  have harg : 2 * (Real.pi : ℂ) * Complex.I * ((1 / 3 + 1 / 3 : ℝ) : ℂ) =
      (((4 * Real.pi / 3 : ℝ) : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [harg, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin] at hre
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    mul_zero, Complex.ofReal_im, mul_one, sub_zero, add_zero] at hre
  have hcos : Real.cos (4 * Real.pi / 3) = -(1 / 2 : ℝ) := by
    rw [show (4 * Real.pi / 3 : ℝ) = Real.pi / 3 + Real.pi by ring,
      Real.cos_add_pi, Real.cos_pi_div_three]
  rw [hcos] at hre
  norm_num at hre

/-- **Tate's Opposite-Sign Global Adelic Character Triviality on `ℚ`**:
Whenever a rational `q : ℚ` decomposes as an integer plus a finite sum of
`p`-adic principal parts `∑ i ∈ s, frac i` (`(∑ i ∈ s, frac i) - q = n` for
`n : ℤ`), the product of the negative-sign Archimedean character at `q` and
the positive-sign finite-place characters equals `1`. -/
theorem tate_opposite_sign_character_trivial_on_rat
    {ι : Type*} (s : Finset ι) (q : ℚ) (frac : ι → ℚ) (n : ℤ)
    (hdecomp : (∑ i ∈ s, (frac i : ℝ)) - (q : ℝ) = (n : ℝ)) :
    addCharNeg (q : ℝ) * (∏ i ∈ s, addCharPos (frac i : ℝ)) = 1 := by
  rw [addCharPos_finset_sum, addCharNeg_mul_addCharPos, hdecomp]
  exact addCharPos_int n

/-- Concrete `q = 1 / 3` verification of Tate's opposite-sign cancellation. -/
theorem tate_opposite_sign_at_one_third :
    addCharNeg (1 / 3 : ℝ) * addCharPos (1 / 3 : ℝ) = 1 := by
  rw [addCharNeg_mul_addCharPos, sub_self]
  simpa using addCharPos_int 0

/-! ## 2. Odd-character erasure by even indicators vs. shifted coset non-vanishing -/

/-- **Even-indicator erasure theorem**:
For any finite modulus `m`, any odd character `χ : (ZMod m)ˣ →* ℂ` (`χ (-1) = -1`),
and any even test function `f : (ZMod m)ˣ → ℂ` (`∀ u, f (-u) = f u`, e.g. any
origin-centered subgroup indicator `1_{K_v}`), the character sum vanishes identically. -/
theorem odd_char_sum_even_test_eq_zero
    (m : ℕ) [NeZero m] (χ : (ZMod m)ˣ →* ℂ) (hodd : χ (-1) = -1)
    (f : (ZMod m)ˣ → ℂ) (heven : ∀ u, f (-u) = f u) :
    (∑ u : (ZMod m)ˣ, χ u * f u) = 0 := by
  have hneg :
      (∑ u : (ZMod m)ˣ, χ u * f u) = -(∑ u : (ZMod m)ˣ, χ u * f u) := by
    calc
      (∑ u : (ZMod m)ˣ, χ u * f u) =
          ∑ u : (ZMod m)ˣ, χ ((-1 : (ZMod m)ˣ) * u) * f ((-1 : (ZMod m)ˣ) * u) := by
            exact (Equiv.sum_comp (Equiv.mulLeft (-1 : (ZMod m)ˣ))
              (fun u => χ u * f u)).symm
      _ = ∑ u : (ZMod m)ˣ, -(χ u * f u) := by
            refine Finset.sum_congr rfl ?_
            intro u _
            have hnu : (-1 : (ZMod m)ˣ) * u = -u := Units.ext (by simp)
            rw [map_mul, hodd, hnu, heven u]
            simp
      _ = -(∑ u : (ZMod m)ˣ, χ u * f u) := by rw [Finset.sum_neg_distrib]
  have h2 : (2 : ℂ) * (∑ u : (ZMod m)ˣ, χ u * f u) = 0 := by
    rw [two_mul]
    exact add_eq_zero_iff_eq_neg.mpr hneg
  exact (mul_eq_zero.mp h2).resolve_left (by norm_num)

/-- Shifted coset indicator `1_{a}` on `(ZMod m)ˣ` (finite-level shadow of `1_{a + pℤ_p}`). -/
def shiftedCosetIndicator {m : ℕ} (a : (ZMod m)ˣ) (u : (ZMod m)ˣ) : ℂ :=
  if u = a then 1 else 0

/-- **Shifted coset non-vanishing**:
Pairing any character `χ : (ZMod m)ˣ →* ℂ` against the shifted coset indicator
`1_{1}` (which is NOT even when `-1 ≠ 1`) evaluates to `1 ≠ 0`. -/
theorem odd_char_shifted_coset_eq_one
    (m : ℕ) [NeZero m] (χ : (ZMod m)ˣ →* ℂ) :
    (∑ u : (ZMod m)ˣ, χ u * shiftedCosetIndicator 1 u) = 1 := by
  rw [Finset.sum_eq_single (1 : (ZMod m)ˣ)]
  · simp [shiftedCosetIndicator]
  · intro u _ hu
    simp [shiftedCosetIndicator, hu]
  · intro h1
    exact (h1 (Finset.mem_univ _)).elim

/-- Complex-valued quadratic character mod `3`, lifting `primeQuadCharHom 3` from
`CyclotomicQuadraticBooleanSignBridge`. -/
def quadCharMod3 : (ZMod 3)ˣ →* ℂ :=
  (Int.castRingHom ℂ).toMonoidHom.comp ((Units.coeHom ℤ).comp (primeQuadCharHom 3))

/-- **Concrete prime `p = 3` odd-character witness**:
`quadCharMod3` is genuinely odd (`quadCharMod3 (-1) = -1`), so every even test
function annihilates it, while the shifted coset `1_{1}` evaluates to `1 ≠ 0`. -/
theorem odd_quad_char_mod3_witness :
    (quadCharMod3 (-1) = -1) ∧
    (∀ f : (ZMod 3)ˣ → ℂ, (∀ u, f (-u) = f u) →
      (∑ u : (ZMod 3)ˣ, quadCharMod3 u * f u) = 0) ∧
    ((∑ u : (ZMod 3)ˣ, quadCharMod3 u * shiftedCosetIndicator 1 u) = 1) := by
  have hodd : quadCharMod3 (-1) = -1 := by
    have hq : quadraticChar (ZMod 3) (-1 : ZMod 3) = -1 := by
      have hchar : ringChar (ZMod 3) ≠ 2 := by
        rw [ZMod.ringChar_zmod_n]
        decide
      rw [quadraticChar_neg_one hchar]
      norm_num [ZMod.card]
    change (((primeQuadCharHom 3 (-1) : ℤˣ) : ℤ) : ℂ) = -1
    have hval : ((primeQuadCharHom 3 (-1) : ℤˣ) : ℤ) = -1 := hq
    rw [hval]
    norm_num
  exact ⟨hodd, fun f hf => odd_char_sum_even_test_eq_zero 3 quadCharMod3 hodd f hf,
    odd_char_shifted_coset_eq_one 3 quadCharMod3⟩

end InfoGeometry.Arithmetic.TateAdelicSignAndOddCharacterCosetBridge
