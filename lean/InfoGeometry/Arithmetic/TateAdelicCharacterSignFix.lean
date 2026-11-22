/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Int.GCD

/-!
# Tate's Global Adelic Character Sign Convention (`F13` / `I29`)

Formalizes the sign fix for the standard global additive character `ψ_ℚ` on `𝔸_ℚ`
documented in `riemann-masullo` `ERRATA.md` items `F13` and `I29`:

1. With the standard circle character `e(x) = exp(2πi x)`, the same-sign product
   `e(x_∞) · e(x_3)` is **nontrivial** on the diagonal rational `1/3 ∈ ℚ`:
   `e(1/3) · e(1/3) = e(2/3) ≠ 1`.
2. Reversing the sign at finite places (`e(x_∞) · ∏_{p ∈ S} e(-frac_p)`) makes the
   global character **identically `1`** on every rational decomposition
   `q = m + ∑_{p ∈ S} frac_p` (`m : ℤ`).
3. By Bézout's identity, every rational with coprime denominator factorization
   `n / (a * b)` decomposes into `c / a + d / b`, yielding global triviality on
   all finite-place coprime factorizations.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.TateAdelicCharacterSignFix

/-- Standard additive circle character `e(x) = exp(2πi x)`. -/
def stdChar (x : ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))

theorem stdChar_zero : stdChar 0 = 1 := by
  simp [stdChar]

theorem stdChar_add (x y : ℝ) : stdChar (x + y) = stdChar x * stdChar y := by
  unfold stdChar
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem stdChar_neg (x : ℝ) : stdChar (-x) = (stdChar x)⁻¹ := by
  unfold stdChar
  rw [← Complex.exp_neg]
  congr 1
  push_cast
  ring

theorem stdChar_mul_neg (x : ℝ) : stdChar x * stdChar (-x) = 1 := by
  rw [← stdChar_add, add_neg_cancel, stdChar_zero]

theorem stdChar_int (n : ℤ) : stdChar (n : ℝ) = 1 := by
  unfold stdChar
  have h : (2 : ℂ) * Real.pi * Complex.I * ((n : ℝ) : ℂ) =
      (n : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [h]
  exact Complex.exp_int_mul_two_pi_mul_I n

theorem stdChar_add_int (x : ℝ) (n : ℤ) : stdChar (x + n) = stdChar x := by
  rw [stdChar_add, stdChar_int, mul_one]

/-- Finite product of `stdChar` equals `stdChar` of the sum. -/
theorem prod_stdChar {ι : Type*} (S : Finset ι) (f : ι → ℝ) :
    (∏ i ∈ S, stdChar (f i)) = stdChar (∑ i ∈ S, f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [stdChar_zero]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, stdChar_add]

/-! ## 1. `F13` / `I29` Refutation of the Printed Same-Sign Adelic Character -/

/-- Same-sign product `e(1/3) * e(1/3)` equals `e(2/3)`, whose imaginary part is
`sin(4π/3) = -√3/2 ≠ 0`, hence `e(1/3) * e(1/3) ≠ 1`. -/
theorem printed_same_sign_char_ne_one_at_one_third :
    stdChar (1 / 3 : ℝ) * stdChar (1 / 3 : ℝ) ≠ 1 := by
  rw [← stdChar_add]
  intro h
  have him := congrArg Complex.im h
  have harg : (2 : ℂ) * Real.pi * Complex.I * (((1 / 3 : ℝ) + (1 / 3 : ℝ) : ℝ) : ℂ) =
      ((4 * Real.pi / 3 : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  simp only [stdChar, harg, Complex.exp_mul_I, Complex.add_im,
    Complex.mul_im, Complex.I_re, Complex.I_im, Complex.one_im, mul_zero, mul_one,
    zero_add, Complex.cos_ofReal_im, Complex.sin_ofReal_re] at him
  have hsin : Real.sin (4 * Real.pi / 3) = -(Real.sqrt 3 / 2) := by
    have h43 : (4 * Real.pi / 3 : ℝ) = Real.pi / 3 + Real.pi := by ring
    rw [h43, Real.sin_add_pi, Real.sin_pi_div_three]
  rw [hsin] at him
  have hpos : (0 : ℝ) < Real.sqrt 3 / 2 := by positivity
  linarith

/-! ## 2. Tate's Opposite-Sign Global Character Triviality on `ℚ` -/

/-- Opposite-sign Tate global character evaluated on an Archimedean coordinate `x_∞`
and a finite family of finite-place principal parts `frac_p` (`p ∈ S`). -/
def tateGlobalChar {ι : Type*} (S : Finset ι) (xInf : ℝ) (frac : ι → ℝ) : ℂ :=
  stdChar xInf * ∏ p ∈ S, stdChar (-(frac p))

/-- **Tate Global Triviality Theorem**: Whenever `xInf` differs from the sum of
finite-place principal parts `∑ p ∈ S, frac p` by an integer `m : ℤ`, the
opposite-sign global character evaluates identically to `1`. -/
theorem tateGlobalChar_eq_one_of_int_diff {ι : Type*} (S : Finset ι)
    (xInf : ℝ) (frac : ι → ℝ) (m : ℤ)
    (hdecomp : xInf = (m : ℝ) + ∑ p ∈ S, frac p) :
    tateGlobalChar S xInf frac = 1 := by
  unfold tateGlobalChar
  rw [prod_stdChar, ← stdChar_add, Finset.sum_neg_distrib, hdecomp]
  have hcancel : (m : ℝ) + (∑ p ∈ S, frac p) + -(∑ p ∈ S, frac p) = (m : ℝ) := by
    ring
  rw [hcancel, stdChar_int]

/-- At `q = 1/3` with `S = {3}`, the corrected opposite-sign Tate character is `1`. -/
theorem tateGlobalChar_one_third_eq_one :
    tateGlobalChar ({3} : Finset ℕ) (1 / 3 : ℝ) (fun _ => (1 / 3 : ℝ)) = 1 :=
  tateGlobalChar_eq_one_of_int_diff ({3} : Finset ℕ) (1 / 3 : ℝ) (fun _ => (1 / 3 : ℝ)) 0
    (by norm_num)

/-- Bézout partial-fraction split for any coprime positive integers `a, b`:
every fraction `n / (a * b)` splits into `c / a + d / b` in `ℚ`. -/
theorem rat_partial_fraction_coprime (n : ℤ) {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hcop : Nat.Coprime a b) :
    ∃ c d : ℤ, (n : ℚ) / ((a * b : ℕ) : ℚ) = (c : ℚ) / (a : ℚ) + (d : ℚ) / (b : ℚ) := by
  refine ⟨n * Nat.gcdB a b, n * Nat.gcdA a b, ?_⟩
  have hbez : ((a : ℤ) * Nat.gcdA a b + (b : ℤ) * Nat.gcdB a b : ℤ) = 1 := by
    have h := Nat.gcd_eq_gcd_ab a b
    rw [hcop.gcd_eq_one] at h
    exact h.symm
  have hbezQ : (a : ℚ) * (Nat.gcdA a b : ℚ) + (b : ℚ) * (Nat.gcdB a b : ℚ) = 1 := by
    exact_mod_cast hbez
  have haQ : (a : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr ha
  have hbQ : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hb
  push_cast
  field_simp [haQ, hbQ]
  linear_combination (n : ℚ) * hbezQ.symm

/-- For any rational `n / (a * b)` with coprime denominators `a, b`, the two-place
opposite-sign Tate character evaluates identically to `1`. -/
theorem tateGlobalChar_coprime_pair_eq_one (n : ℤ) {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hcop : Nat.Coprime a b) :
    ∃ c d : ℤ,
      tateGlobalChar (Finset.univ : Finset (Fin 2))
        (((n : ℚ) / ((a * b : ℕ) : ℚ) : ℚ) : ℝ)
        (fun i => if i = 0 then (((c : ℚ) / (a : ℚ) : ℚ) : ℝ)
                  else (((d : ℚ) / (b : ℚ) : ℚ) : ℝ)) = 1 := by
  obtain ⟨c, d, hsplit⟩ := rat_partial_fraction_coprime n ha hb hcop
  refine ⟨c, d, tateGlobalChar_eq_one_of_int_diff Finset.univ _ _ 0 ?_⟩
  simp only [Int.cast_zero, zero_add, Fin.sum_univ_two, ite_true,
    show (1 : Fin 2) ≠ 0 by decide, ite_false]
  exact_mod_cast hsplit

end InfoGeometry.Arithmetic.TateAdelicCharacterSignFix
