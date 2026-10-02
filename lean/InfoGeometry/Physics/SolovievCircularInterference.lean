import InfoGeometry.Physics.SolovievPhononCorrections

noncomputable section

namespace InfoGeometry.Physics.SolovievCircularInterference

open SolovievPhononCorrections
open NuclearQuasiparticleCAR

@[simp] theorem circularAmplitude_re (amplitude sign : ℝ) :
    (circularAmplitude amplitude sign).re = amplitude / (2 * Real.sqrt 2) := by
  simp only [circularAmplitude, Complex.mul_re, Complex.mul_im, Complex.add_re,
    Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.one_re,
    Complex.one_im, Complex.I_re, Complex.I_im]
  ring

@[simp] theorem circularAmplitude_im (amplitude sign : ℝ) :
    (circularAmplitude amplitude sign).im = amplitude / (2 * Real.sqrt 2) * sign := by
  simp only [circularAmplitude, Complex.mul_re, Complex.mul_im, Complex.add_re,
    Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.one_re,
    Complex.one_im, Complex.I_re, Complex.I_im]
  ring

theorem circularAmplitude_conj (amplitude sign : ℝ) :
    starRingEnd ℂ (circularAmplitude amplitude sign) = circularAmplitude amplitude (-sign) := by
  apply Complex.ext <;> simp

theorem circularAmplitude_not_pure_imaginary (amplitude sign : ℝ)
    (nonzero : amplitude ≠ 0) : (circularAmplitude amplitude sign).re ≠ 0 := by
  rw [circularAmplitude_re]
  exact div_ne_zero nonzero (mul_ne_zero (by norm_num) (ne_of_gt (Real.sqrt_pos.2 (by norm_num))))

theorem circularAmplitude_add (first second sign : ℝ) :
    circularAmplitude first sign + circularAmplitude second sign =
      circularAmplitude (first + second) sign := by
  apply Complex.ext <;> simp <;> ring

theorem circular_strength_decomposition (orbital spin sign : ℝ) (sign_sq : sign ^ 2 = 1) :
    Complex.normSq (circularAmplitude orbital sign + circularAmplitude spin sign) =
      orbital ^ 2 / 4 + spin ^ 2 / 4 + orbital * spin / 2 := by
  rw [circularAmplitude_add, circularAmplitude_normSq _ _ sign_sq]
  ring

theorem circular_strength_zero_iff (orbital spin sign : ℝ) (sign_sq : sign ^ 2 = 1) :
    Complex.normSq (circularAmplitude orbital sign + circularAmplitude spin sign) = 0 ↔
      spin = -orbital := by
  rw [circularAmplitude_add, circularAmplitude_normSq _ _ sign_sq]
  constructor
  · intro zero
    have square_zero : (orbital + spin) ^ 2 = 0 := by linarith
    have sum_zero := (sq_eq_zero_iff).mp square_zero
    linarith
  · intro opposite
    simp [opposite]

theorem strength_suppressed_iff (orbital spin : ℂ) :
    Complex.normSq (orbital + spin) < Complex.normSq orbital + Complex.normSq spin ↔
      (orbital * starRingEnd ℂ spin).re < 0 := by
  rw [Complex.normSq_add]
  constructor <;> intro inequality <;> linarith

theorem strength_zero_iff (orbital spin : ℂ) :
    Complex.normSq (orbital + spin) = 0 ↔ spin = -orbital := by
  rw [Complex.normSq_eq_zero]
  exact add_eq_zero_iff_eq_neg'

theorem circular_phonon_split {Index Operator : Type*} [DecidableEq Index]
    [Ring Operator] [Algebra ℂ Operator] (car : QuasiparticleCAR Index Operator)
    (first second : Index) (forward backward sign : ℝ) :
    phononCreation car first second
        (circularAmplitude forward sign) (circularAmplitude backward (-sign)) =
      (((forward / (2 * Real.sqrt 2) : ℝ) : ℂ) • (car.adag first * car.adag second) -
        ((backward / (2 * Real.sqrt 2) : ℝ) : ℂ) • (car.a second * car.a first)) +
      (Complex.I * (sign : ℂ)) •
        (((forward / (2 * Real.sqrt 2) : ℝ) : ℂ) • (car.adag first * car.adag second) +
          ((backward / (2 * Real.sqrt 2) : ℝ) : ℂ) • (car.a second * car.a first)) := by
  simp only [phononCreation, circularAmplitude, Complex.ofReal_neg]
  module

end InfoGeometry.Physics.SolovievCircularInterference
