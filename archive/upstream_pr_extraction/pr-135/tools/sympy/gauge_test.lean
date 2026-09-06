import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Tactic.Ring

noncomputable section

def QuaternionicField := Fin 2 → ℂ

def U1_Action (θ : ℝ) (Φ : QuaternionicField) : QuaternionicField :=
  fun i => (Complex.exp (θ * Complex.I)) * Φ i

theorem U1_norm_preservation (θ : ℝ) (Φ : QuaternionicField) :
    Complex.normSq (U1_Action θ Φ 0) + Complex.normSq (U1_Action θ Φ 1) = 
    Complex.normSq (Φ 0) + Complex.normSq (Φ 1) := by
  unfold U1_Action
  simp only [Complex.normSq_mul]
  have h_exp : Complex.normSq (Complex.exp (θ * Complex.I)) = 1 := by
    have h1 : Complex.exp ((θ : ℂ) * Complex.I) = Complex.cos (θ : ℂ) + Complex.sin (θ : ℂ) * Complex.I := Complex.exp_mul_I (θ : ℂ)
    rw [h1]
    have h_re : (Complex.cos (θ : ℂ) + Complex.sin (θ : ℂ) * Complex.I).re = Real.cos θ := by 
      simp only [Complex.add_re, Complex.mul_re, Complex.I_re, mul_zero, Complex.I_im, mul_one, sub_zero, Complex.cos_ofReal_re, Complex.sin_ofReal_im]
      ring
    have h_im : (Complex.cos (θ : ℂ) + Complex.sin (θ : ℂ) * Complex.I).im = Real.sin θ := by 
      simp only [Complex.add_im, Complex.mul_im, Complex.I_re, mul_zero, Complex.I_im, mul_one, add_zero, Complex.cos_ofReal_im, Complex.sin_ofReal_re, zero_add]
    have h_norm : Complex.normSq (Complex.cos (θ : ℂ) + Complex.sin (θ : ℂ) * Complex.I) = Real.cos θ ^ 2 + Real.sin θ ^ 2 := by
      rw [Complex.normSq_apply]
      rw [h_re, h_im]
      ring
    rw [h_norm]
    exact Real.cos_sq_add_sin_sq θ
  rw [h_exp]
  ring
