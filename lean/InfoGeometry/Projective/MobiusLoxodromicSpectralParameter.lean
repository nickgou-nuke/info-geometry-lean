import InfoGeometry.Projective.MobiusWindingRootBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Projective.MobiusGauge

/-!
# Finite complex loxodromic spectral parameter

This owner adds only the complex spectral readout missing from the real
Cartan/root owner.  It does not claim a global logarithm or a classification
of all Möbius conjugacy classes.
-/

namespace InfoGeometry.Projective.MobiusLoxodromicSpectralParameter

abbrev Matrix2 := InfoGeometry.Algebra.FiniteSpin.Mat2C

noncomputable def flow (κ : ℂ) : Matrix2 :=
  !![Complex.exp κ, 0; 0, Complex.exp (-κ)]

def plusVector : Fin 2 → ℂ := ![1, 0]

def minusVector : Fin 2 → ℂ := ![0, 1]

theorem flow_apply_plus (κ : ℂ) :
    (flow κ).mulVec plusVector = (Complex.exp κ) • plusVector := by
  ext i
  fin_cases i <;> simp [flow, plusVector, Matrix.mulVec, dotProduct]

theorem flow_apply_minus (κ : ℂ) :
    (flow κ).mulVec minusVector = (Complex.exp (-κ)) • minusVector := by
  ext i
  fin_cases i <;> simp [flow, minusVector, Matrix.mulVec, dotProduct]

theorem flow_neg (κ : ℂ) :
    flow (-κ) = !![Complex.exp (-κ), 0; 0, Complex.exp κ] := by
  simp [flow, neg_neg]

theorem flow_inverse (κ : ℂ) :
    flow κ * flow (-κ) = (1 : Matrix2) := by
  rw [flow_neg]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [flow, Matrix.mul_apply, Fin.sum_univ_two, ← Complex.exp_add]

theorem flow_neg_inverse (κ : ℂ) :
    flow (-κ) * flow κ = (1 : Matrix2) := by
  rw [flow_neg]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [flow, Matrix.mul_apply, Fin.sum_univ_two, ← Complex.exp_add]

theorem spectral_parameter_inversion (κ : ℂ) :
    Complex.exp (-κ) = (Complex.exp κ)⁻¹ := by
  rw [← Complex.exp_neg]

/-! ## The logarithmic deck coordinate of the loxodromic parameter -/

noncomputable def deckRapidity (κ : ℂ) (n : ℤ) : ℂ :=
  κ + (n : ℂ) * (Real.pi * Complex.I)

theorem deckRapidity_zero (κ : ℂ) :
    deckRapidity κ 0 = κ := by
  simp [deckRapidity]

theorem deckRapidity_add (κ : ℂ) (n k : ℤ) :
    deckRapidity κ (n + k) =
      deckRapidity κ n + (k : ℂ) * (Real.pi * Complex.I) := by
  unfold deckRapidity
  rw [Int.cast_add]
  ring

theorem deckRapidity_exp_two_invariant (κ : ℂ) (n : ℤ) :
    Complex.exp (2 * deckRapidity κ n) = Complex.exp (2 * κ) := by
  unfold deckRapidity
  rw [show 2 * (κ + (n : ℂ) * (Real.pi * Complex.I)) =
      2 * κ + (n : ℂ) * (2 * Real.pi * Complex.I) by ring,
    Complex.exp_add]
  rw [Complex.exp_int_mul_two_pi_mul_I]
  simp

theorem deckRapidity_inversion (κ : ℂ) (n : ℤ) :
    deckRapidity (-κ) n = -deckRapidity κ (-n) := by
  unfold deckRapidity
  rw [Int.cast_neg]
  ring

def exchange : Matrix2 := !![(0 : ℂ), 1; 1, 0]

theorem flow_det (κ : ℂ) :
    (flow κ).det = 1 := by
  simp [flow, Matrix.det_fin_two, ← Complex.exp_add]

theorem flow_trace (κ : ℂ) :
    Matrix.trace (flow κ) = Complex.exp κ + Complex.exp (-κ) := by
  simp [flow, Matrix.trace, Fin.sum_univ_two]

theorem exchange_sq : exchange * exchange = (1 : Matrix2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [exchange, Matrix.mul_apply, Fin.sum_univ_two]

theorem exchange_conjugates_flow (κ : ℂ) :
    exchange * flow κ * exchange = flow (-κ) := by
  rw [flow_neg]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [exchange, flow, Matrix.mul_apply, Fin.sum_univ_two]

def complexRapidity (η θ : ℝ) : ℂ :=
  (η : ℂ) + Complex.I * (θ : ℂ)

theorem complexRapidity_real_part (η θ : ℝ) :
    (complexRapidity η θ).re = η := by
  simp [complexRapidity]

theorem complexRapidity_imag_part (η θ : ℝ) :
    (complexRapidity η θ).im = θ := by
    simp [complexRapidity]

noncomputable def asMobius (κ : ℂ) : MobiusMap ℂ :=
  { α := Complex.exp κ
    β := 0
    γ := 0
    δ := Complex.exp (-κ)
    det_ne_zero := by
      simp [← Complex.exp_add] }

theorem asMobius_action (κ z : ℂ) :
    projectiveAction (asMobius κ) z = Complex.exp (2 * κ) * z := by
  simp only [projectiveAction, asMobius]
  rw [show Complex.exp (-κ) = (Complex.exp κ)⁻¹ by
    exact spectral_parameter_inversion κ]
  simp
  calc
    Complex.exp κ * z * Complex.exp κ =
        (Complex.exp κ * Complex.exp κ) * z := by ring
    _ = Complex.exp (κ + κ) * z := by rw [← Complex.exp_add]
    _ = Complex.exp (2 * κ) * z := by
      rw [show κ + κ = 2 * κ by ring]

theorem asMobius_deckRapidity_action (κ z : ℂ) (n : ℤ) :
    projectiveAction (asMobius (deckRapidity κ n)) z =
      projectiveAction (asMobius κ) z := by
  rw [asMobius_action, asMobius_action, deckRapidity_exp_two_invariant]

end InfoGeometry.Projective.MobiusLoxodromicSpectralParameter
