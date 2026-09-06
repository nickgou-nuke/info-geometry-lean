import Mathlib
import InfoGeometry.Canonical.TwelveFoldDirichletCharacters
import InfoGeometry.Canonical.TwelveFoldAdditiveCharacter

/-!
# The primitive twelvefold Dirichlet Gauss sum

This owner uses Mathlib's native `gaussSum` and Fourier-transform theorem.
It deliberately keeps `ZMod.stdAddChar` explicit: the additive character
defined from the chosen `zeta12` phase is a separate convention-transport
problem, not a definitional equality.
-/

noncomputable section

namespace InfoGeometry.Canonical.TwelveFoldGaussSum

open InfoGeometry.Canonical.TwelveFoldDirichlet
open InfoGeometry.Canonical.TwelveFoldAdditiveCharacter

/-- The native Gauss sum of the primitive mixed character modulo twelve. -/
def gaussSum12 : ℂ := gaussSum chiTwelve ZMod.stdAddChar

theorem chiTwelve_isPrimitive : chiTwelve.IsPrimitive := by
  rw [DirichletCharacter.isPrimitive_def]
  exact chiTwelve_conductor_eq_twelve

/-- Native Mathlib Fourier identity specialized to the mixed level-12 character. -/
theorem chiTwelve_fourierTransform_eq_gaussSum (k : ZMod 12) :
    ZMod.dft (chiTwelve : ZMod 12 → ℂ) k =
      chiTwelve⁻¹ (-k) * gaussSum12 := by
  letI : NeZero (12 : ℕ) := ⟨by norm_num⟩
  simpa [gaussSum12] using
    (chiTwelve_isPrimitive.fourierTransform_eq_inv_mul_gaussSum k)

/-- The same Gauss sum with the explicitly chosen primitive additive character. -/
def chosenGaussSum12 : ℂ := gaussSum chiTwelve additiveCharacter12

private lemma chiTwelve_value_zero : chiTwelve (0 : ZMod 12) = 0 := by
  exact chiTwelve_nonunit 0 (by decide)

private lemma chiTwelve_value_one : chiTwelve (1 : ZMod 12) = 1 := by
  convert chiTwelve_unitOne using 1 <;> decide

private lemma chiTwelve_value_two : chiTwelve (2 : ZMod 12) = 0 := by
  exact chiTwelve_nonunit 2 (by decide)

private lemma chiTwelve_value_three : chiTwelve (3 : ZMod 12) = 0 := by
  exact chiTwelve_nonunit 3 (by decide)

private lemma chiTwelve_value_four : chiTwelve (4 : ZMod 12) = 0 := by
  exact chiTwelve_nonunit 4 (by decide)

private lemma chiTwelve_value_five : chiTwelve (5 : ZMod 12) = -1 := by
  convert chiTwelve_unitFive using 1 <;> decide

private lemma chiTwelve_value_six : chiTwelve (6 : ZMod 12) = 0 := by
  exact chiTwelve_nonunit 6 (by decide)

private lemma chiTwelve_value_seven : chiTwelve (7 : ZMod 12) = -1 := by
  convert chiTwelve_unitSeven using 1 <;> decide

private lemma chiTwelve_value_eight : chiTwelve (8 : ZMod 12) = 0 := by
  exact chiTwelve_nonunit 8 (by decide)

private lemma chiTwelve_value_nine : chiTwelve (9 : ZMod 12) = 0 := by
  exact chiTwelve_nonunit 9 (by decide)

private lemma chiTwelve_value_ten : chiTwelve (10 : ZMod 12) = 0 := by
  exact chiTwelve_nonunit 10 (by decide)

private lemma chiTwelve_value_eleven : chiTwelve (11 : ZMod 12) = 1 := by
  convert chiTwelve_unitEleven using 1 <;> decide

theorem chosenGaussSum12_expansion :
    chosenGaussSum12 = zeta12 - zeta12 ^ 5 - zeta12 ^ 7 + zeta12 ^ 11 := by
  classical
  have h0 : ZMod.finEquiv 12 (0 : Fin 12) = (0 : ZMod 12) := by decide
  have h1 : ZMod.finEquiv 12 (1 : Fin 12) = (1 : ZMod 12) := by decide
  have h2 : ZMod.finEquiv 12 (2 : Fin 12) = (2 : ZMod 12) := by decide
  have h3 : ZMod.finEquiv 12 (3 : Fin 12) = (3 : ZMod 12) := by decide
  have h4 : ZMod.finEquiv 12 (4 : Fin 12) = (4 : ZMod 12) := by decide
  have h5 : ZMod.finEquiv 12 (5 : Fin 12) = (5 : ZMod 12) := by decide
  have h6 : ZMod.finEquiv 12 (6 : Fin 12) = (6 : ZMod 12) := by decide
  have h7 : ZMod.finEquiv 12 (7 : Fin 12) = (7 : ZMod 12) := by decide
  have h8 : ZMod.finEquiv 12 (8 : Fin 12) = (8 : ZMod 12) := by decide
  have h9 : ZMod.finEquiv 12 (9 : Fin 12) = (9 : ZMod 12) := by decide
  have h10 : ZMod.finEquiv 12 (10 : Fin 12) = (10 : ZMod 12) := by decide
  have h11 : ZMod.finEquiv 12 (11 : Fin 12) = (11 : ZMod 12) := by decide
  change (∑ a : ZMod 12, chiTwelve a * additiveCharacter12 a) = _
  rw [← Fintype.sum_equiv (ZMod.finEquiv 12)
    (fun i : Fin 12 => chiTwelve ((ZMod.finEquiv 12) i) *
      additiveCharacter12 ((ZMod.finEquiv 12) i))
    (fun a : ZMod 12 => chiTwelve a * additiveCharacter12 a) (by intro i; rfl)]
  simp [Fin.sum_univ_succ, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
    additiveCharacter12_apply, chiTwelve_value_zero, chiTwelve_value_one,
    chiTwelve_value_two, chiTwelve_value_three, chiTwelve_value_four,
    chiTwelve_value_five, chiTwelve_value_six, chiTwelve_value_seven,
    chiTwelve_value_eight, chiTwelve_value_nine, chiTwelve_value_ten,
    chiTwelve_value_eleven]
  have hv1 : (1 : ZMod 12).val = 1 := by decide
  have hv5 : (5 : ZMod 12).val = 5 := by decide
  have hv7 : (7 : ZMod 12).val = 7 := by decide
  have hv11 : (11 : ZMod 12).val = 11 := by decide
  rw [hv1, hv5, hv7, hv11]
  ring

theorem zeta12_algebraic :
    zeta12 = ((Real.sqrt 3 / 2 : ℝ) : ℂ) + (1 / 2 : ℂ) * Complex.I := by
  unfold zeta12
  have harg : (2 * Real.pi * Complex.I / 12 : ℂ) =
      ((Real.pi / 6 : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [harg]
  apply Complex.ext
  · rw [Complex.exp_ofReal_mul_I_re, Real.cos_pi_div_six]
    norm_num
  · rw [Complex.exp_ofReal_mul_I_im, Real.sin_pi_div_six]
    norm_num

theorem chosenGaussSum12_eq_two_sqrt_three :
    chosenGaussSum12 = ((2 * Real.sqrt 3 : ℝ) : ℂ) := by
  rw [chosenGaussSum12_expansion, zeta12_algebraic]
  have hsqrt : (Real.sqrt (3 : ℝ)) ^ 2 = 3 := by norm_num
  have hpow2 :
      (((Real.sqrt 3 / 2 : ℝ) : ℂ) + (1 / 2 : ℂ) * Complex.I) ^ 2 =
        ((1 / 2 : ℝ) : ℂ) + ((Real.sqrt 3 / 2 : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;>
      norm_num [pow_two, Complex.add_re, Complex.add_im, Complex.mul_re,
        Complex.mul_im, Complex.I_re, Complex.I_im] <;>
      nlinarith [hsqrt]
  have hpow3 :
      (((Real.sqrt 3 / 2 : ℝ) : ℂ) + (1 / 2 : ℂ) * Complex.I) ^ 3 = Complex.I := by
    calc
      (((Real.sqrt 3 / 2 : ℝ) : ℂ) + (1 / 2 : ℂ) * Complex.I) ^ 3 =
          (((Real.sqrt 3 / 2 : ℝ) : ℂ) + (1 / 2 : ℂ) * Complex.I) ^ 2 *
            (((Real.sqrt 3 / 2 : ℝ) : ℂ) + (1 / 2 : ℂ) * Complex.I) := by ring
      _ = (((1 / 2 : ℝ) : ℂ) + ((Real.sqrt 3 / 2 : ℝ) : ℂ) * Complex.I) *
            (((Real.sqrt 3 / 2 : ℝ) : ℂ) + (1 / 2 : ℂ) * Complex.I) := by rw [hpow2]
      _ = Complex.I := by
        apply Complex.ext <;>
          norm_num [Complex.add_re, Complex.add_im, Complex.mul_re,
            Complex.mul_im, Complex.I_re, Complex.I_im] <;>
          nlinarith [hsqrt]
  have hpow5 :
      (((Real.sqrt 3 / 2 : ℝ) : ℂ) + (1 / 2 : ℂ) * Complex.I) ^ 5 =
        ((-Real.sqrt 3 / 2 : ℝ) : ℂ) + (1 / 2 : ℂ) * Complex.I := by
    calc
      (((Real.sqrt 3 / 2 : ℝ) : ℂ) + (1 / 2 : ℂ) * Complex.I) ^ 5 =
          (((Real.sqrt 3 / 2 : ℝ) : ℂ) + (1 / 2 : ℂ) * Complex.I) ^ 3 *
            (((Real.sqrt 3 / 2 : ℝ) : ℂ) + (1 / 2 : ℂ) * Complex.I) ^ 2 := by ring
      _ = Complex.I * (((1 / 2 : ℝ) : ℂ) +
            ((Real.sqrt 3 / 2 : ℝ) : ℂ) * Complex.I) := by rw [hpow3, hpow2]
      _ = ((-Real.sqrt 3 / 2 : ℝ) : ℂ) + (1 / 2 : ℂ) * Complex.I := by
        apply Complex.ext <;>
          norm_num [Complex.add_re, Complex.add_im, Complex.mul_re,
            Complex.mul_im, Complex.I_re, Complex.I_im] <;>
          ring
  have hpow7 :
      (((Real.sqrt 3 / 2 : ℝ) : ℂ) + (1 / 2 : ℂ) * Complex.I) ^ 7 =
        ((-Real.sqrt 3 / 2 : ℝ) : ℂ) - (1 / 2 : ℂ) * Complex.I := by
    have hpow6 :
        (((Real.sqrt 3 / 2 : ℝ) : ℂ) + (1 / 2 : ℂ) * Complex.I) ^ 6 = -1 := by
      calc
        (((Real.sqrt 3 / 2 : ℝ) : ℂ) + (1 / 2 : ℂ) * Complex.I) ^ 6 =
            ((((Real.sqrt 3 / 2 : ℝ) : ℂ) + (1 / 2 : ℂ) * Complex.I) ^ 3) ^ 2 := by ring
        _ = Complex.I ^ 2 := by rw [hpow3]
        _ = -1 := by norm_num [Complex.I_mul_I]
    calc
      (((Real.sqrt 3 / 2 : ℝ) : ℂ) + (1 / 2 : ℂ) * Complex.I) ^ 7 =
          (((Real.sqrt 3 / 2 : ℝ) : ℂ) + (1 / 2 : ℂ) * Complex.I) ^ 6 *
            (((Real.sqrt 3 / 2 : ℝ) : ℂ) + (1 / 2 : ℂ) * Complex.I) := by ring
      _ = (-1 : ℂ) * (((Real.sqrt 3 / 2 : ℝ) : ℂ) + (1 / 2 : ℂ) * Complex.I) := by rw [hpow6]
      _ = ((-Real.sqrt 3 / 2 : ℝ) : ℂ) - (1 / 2 : ℂ) * Complex.I := by
        norm_num
        ring
  have hpow11 :
      (((Real.sqrt 3 / 2 : ℝ) : ℂ) + (1 / 2 : ℂ) * Complex.I) ^ 11 =
        ((Real.sqrt 3 / 2 : ℝ) : ℂ) - (1 / 2 : ℂ) * Complex.I := by
    have hpow6 :
        (((Real.sqrt 3 / 2 : ℝ) : ℂ) + (1 / 2 : ℂ) * Complex.I) ^ 6 = -1 := by
      calc
        (((Real.sqrt 3 / 2 : ℝ) : ℂ) + (1 / 2 : ℂ) * Complex.I) ^ 6 =
            ((((Real.sqrt 3 / 2 : ℝ) : ℂ) + (1 / 2 : ℂ) * Complex.I) ^ 3) ^ 2 := by ring
        _ = Complex.I ^ 2 := by rw [hpow3]
        _ = -1 := by norm_num [Complex.I_mul_I]
    calc
      (((Real.sqrt 3 / 2 : ℝ) : ℂ) + (1 / 2 : ℂ) * Complex.I) ^ 11 =
          (((Real.sqrt 3 / 2 : ℝ) : ℂ) + (1 / 2 : ℂ) * Complex.I) ^ 6 *
            (((Real.sqrt 3 / 2 : ℝ) : ℂ) + (1 / 2 : ℂ) * Complex.I) ^ 5 := by ring
      _ = (-1 : ℂ) * (((-Real.sqrt 3 / 2 : ℝ) : ℂ) + (1 / 2 : ℂ) * Complex.I) := by rw [hpow6, hpow5]
      _ = ((Real.sqrt 3 / 2 : ℝ) : ℂ) - (1 / 2 : ℂ) * Complex.I := by
        norm_num
        ring
  rw [hpow5, hpow7, hpow11]
  norm_num
  ring

end InfoGeometry.Canonical.TwelveFoldGaussSum
