import Mathlib.Analysis.SpecialFunctions.Pow.Real
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Fisher-Wootters Information Metric, Anscombe Isometry, and Madelung Wave Amplitude (Extended Module)

This module formalizes the exact differential and spectral geometry connecting
information theory, counting statistics, and quantum mechanics:

1. **Fisher-Rao Density for Poisson Counting Statistics:**
   $$g_F(x) = \frac{1}{x}$$
   arising from the variance $\operatorname{Var}(N) = x$.

2. **Wootters / Anscombe Amplitude Isometry:**
   The square-root map $\psi(x) = \sqrt{x}$ is the canonical differential isometry
   between the curved Fisher-Rao statistical manifold and flat Hilbert amplitude space:
   $$4 \left(\frac{d\sqrt{x}}{dx}\right)^2 = \frac{1}{x} = g_F(x)$$

3. **Madelung Quantum Wave on the Critical Line:**
   For any critical exponent $s = \frac{1}{2} + i\gamma$ and scale $x > 0$:
   $$\Psi_\gamma(x) = \sqrt{x} \, (\cos(\gamma \ln x) + i \sin(\gamma \ln x))$$
   satisfies the exact probability norm reconstruction:
   $$\operatorname{normSq}(\Psi_\gamma(x)) = x$$

4. **Geodesic Fisher-Rao Distance Formula:**
   $$d_F(x_1, x_2) = 2 |\sqrt{x_2} - \sqrt{x_1}|$$
   with strict nonnegativity, symmetry, definiteness for positive scales, and collinear additivity.
-/

noncomputable section

namespace InfoGeometry.Canonical.FisherWoottersExtended

open Real Complex

/-! ## 1. Fisher-Rao Metric Density and Anscombe Amplitude -/

/-- The Fisher-Rao information metric density g_F(x) = 1/x for scale/counting statistics -/
def fisherDensity (x : ℝ) : ℝ := 1 / x

/-- The Wootters / Anscombe square-root amplitude map ψ(x) = √x -/
def anscombeAmplitude (x : ℝ) : ℝ := Real.sqrt x

/-- The formal differential algebraic expression: d(√x)/dx = 1 / (2√x) -/
def amplitudeDifferential (x : ℝ) : ℝ := 1 / (2 * Real.sqrt x)

/-- 🏆 THEOREM 1: Exact Probability Reconstruction from Amplitude
    $$\psi(x)^2 = (\sqrt{x})^2 = x$$ -/
theorem anscombe_amplitude_sq {x : ℝ} (hx : 0 ≤ x) :
    (anscombeAmplitude x) ^ 2 = x := by
  dsimp [anscombeAmplitude]
  exact Real.sq_sqrt hx

/-- 🏆 THEOREM 2: Wootters Isometry Identity: 4 · (dψ/dx)² = g_F(x)
    The differential of the square-root map flattens the Fisher-Rao metric. -/
theorem wootters_isometry_identity {x : ℝ} (hx : 0 < x) :
    4 * (amplitudeDifferential x) ^ 2 = fisherDensity x := by
  dsimp [amplitudeDifferential, fisherDensity]
  have h_sqrt_sq : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt (le_of_lt hx)
  have h_denom : (2 * Real.sqrt x) ^ 2 = 4 * x := by
    calc
      (2 * Real.sqrt x) ^ 2 = (2 ^ 2) * ((Real.sqrt x) ^ 2) := mul_pow 2 (Real.sqrt x) 2
      _ = 4 * x := by rw [h_sqrt_sq]; norm_num
  have h_frac_sq : (1 / (2 * Real.sqrt x)) ^ 2 = 1 / (4 * x) := by
    rw [one_div_pow, h_denom]
  rw [h_frac_sq]
  calc
    4 * (1 / (4 * x)) = 4 / (4 * x) := by ring
    _ = (4 * 1) / (4 * x) := by ring
    _ = 1 / x := mul_div_mul_left 1 x (by norm_num)

/-! ## 2. Madelung Quantum Wave on the Critical Line Re(s) = 1/2 -/

/-- The Madelung phase rotor R_γ(x) = cos(γ ln x) + i sin(γ ln x) -/
def madelungRotor (x gamma : ℝ) : ℂ :=
  ⟨Real.cos (gamma * Real.log x), Real.sin (gamma * Real.log x)⟩

/-- 🏆 THEOREM 3: Unimodularity of the Madelung Phase Rotor: |R_γ(x)|² = 1 -/
theorem madelungRotor_normSq (x gamma : ℝ) :
    Complex.normSq (madelungRotor x gamma) = 1 := by
  dsimp [madelungRotor, Complex.normSq]
  have h_pyth : (Real.cos (gamma * Real.log x))^2 + (Real.sin (gamma * Real.log x))^2 = 1 :=
    Real.cos_sq_add_sin_sq (gamma * Real.log x)
  calc
    Real.cos (gamma * Real.log x) * Real.cos (gamma * Real.log x) +
    Real.sin (gamma * Real.log x) * Real.sin (gamma * Real.log x)
      = (Real.cos (gamma * Real.log x))^2 + (Real.sin (gamma * Real.log x))^2 := by ring
    _ = 1 := h_pyth

/-- The critical Mellin-Madelung wave mode ψ_γ(x) = √x · R_γ(x) -/
def criticalMadelungWave (x gamma : ℝ) : ℂ :=
  (Real.sqrt x : ℂ) * madelungRotor x gamma

/-- 🏆 THEOREM 4: Exact Norm Reconstruction of the Critical Wave Mode:
    $$\operatorname{normSq}(\Psi_\gamma(x)) = x$$ -/
theorem criticalMadelungWave_normSq (x gamma : ℝ) (hx : 0 ≤ x) :
    Complex.normSq (criticalMadelungWave x gamma) = x := by
  dsimp [criticalMadelungWave]
  rw [Complex.normSq_mul, Complex.normSq_ofReal]
  have h_rotor : Complex.normSq (madelungRotor x gamma) = 1 := madelungRotor_normSq x gamma
  rw [h_rotor, mul_one]
  have h_sq : Real.sqrt x * Real.sqrt x = (Real.sqrt x) ^ 2 := by ring
  rw [h_sq]
  exact Real.sq_sqrt hx

/-- 🏆 THEOREM 5: Factorization of the Critical Mode into Amplitude and Rotor:
    $$\Psi_\gamma(x) = \psi(x) \cdot R_\gamma(x)$$ -/
theorem criticalMadelungWave_eq_amplitude_mul_rotor (x gamma : ℝ) :
    criticalMadelungWave x gamma =
      (anscombeAmplitude x : ℂ) * madelungRotor x gamma := rfl

/-! ## 3. Geodesic Fisher-Rao Distance Formula -/

/-- Geodesic distance formula on the statistical manifold of Poisson scales -/
def fisherGeodesicDistance (x₁ x₂ : ℝ) : ℝ :=
  2 * |Real.sqrt x₂ - Real.sqrt x₁|

/-- 🏆 THEOREM 6: Non-negativity of the Fisher Geodesic Distance -/
theorem fisherGeodesicDistance_nonneg (x₁ x₂ : ℝ) :
    0 ≤ fisherGeodesicDistance x₁ x₂ := by
  dsimp [fisherGeodesicDistance]
  have h_half_pos : (0 : ℝ) ≤ 2 := by norm_num
  exact mul_nonneg h_half_pos (abs_nonneg _)

/-- 🏆 THEOREM 7: Symmetry of the Fisher Geodesic Distance -/
theorem fisherGeodesicDistance_comm (x₁ x₂ : ℝ) :
    fisherGeodesicDistance x₁ x₂ = fisherGeodesicDistance x₂ x₁ := by
  dsimp [fisherGeodesicDistance]
  rw [abs_sub_comm]

/-- 🏆 THEOREM 8: Definiteness of the Fisher Geodesic Distance for Positive Scales -/
theorem fisherGeodesicDistance_eq_zero_iff {x₁ x₂ : ℝ} (h₁ : 0 ≤ x₁) (h₂ : 0 ≤ x₂) :
    fisherGeodesicDistance x₁ x₂ = 0 ↔ x₁ = x₂ := by
  dsimp [fisherGeodesicDistance]
  constructor
  · intro h
    have h_abs : |Real.sqrt x₂ - Real.sqrt x₁| = 0 := by linarith
    rw [abs_eq_zero] at h_abs
    have h_sqrt_eq : Real.sqrt x₁ = Real.sqrt x₂ := by linarith
    have h1_sq := Real.sq_sqrt h₁
    have h2_sq := Real.sq_sqrt h₂
    calc
      x₁ = (Real.sqrt x₁) ^ 2 := h1_sq.symm
      _ = (Real.sqrt x₂) ^ 2 := by rw [h_sqrt_eq]
      _ = x₂ := h2_sq
  · rintro rfl
    simp

/-- 🏆 THEOREM 9: Collinear Triangle Equality for Monotone Scales (x₁ ≤ x₂ ≤ x₃) -/
theorem fisherGeodesicDistance_collinear {x₁ x₂ x₃ : ℝ}
    (h23 : x₁ ≤ x₂) (h34 : x₂ ≤ x₃) :
    fisherGeodesicDistance x₁ x₂ + fisherGeodesicDistance x₂ x₃ =
      fisherGeodesicDistance x₁ x₃ := by
  have s1_le_s2 : Real.sqrt x₁ ≤ Real.sqrt x₂ := Real.sqrt_le_sqrt h23
  have s2_le_s3 : Real.sqrt x₂ ≤ Real.sqrt x₃ := Real.sqrt_le_sqrt h34
  have _s1_le_s3 : Real.sqrt x₁ ≤ Real.sqrt x₃ := le_trans s1_le_s2 s2_le_s3
  dsimp [fisherGeodesicDistance]
  rw [abs_of_nonneg (by linarith)]
  rw [abs_of_nonneg (by linarith)]
  rw [abs_of_nonneg (by linarith)]
  ring

/-- 🏆 THEOREM 10: MASTER FISHER-WOOTTERS MADELUNG QUANTUM POTENTIAL PACKET -/
theorem master_fisher_wootters_madelung_packet
    {x x₁ x₂ x₃ : ℝ} (gamma : ℝ)
    (hx : 0 < x) (h1 : 0 ≤ x₁) (h2 : 0 ≤ x₂)
    (h23 : x₁ ≤ x₂) (h34 : x₂ ≤ x₃) :
    -- 1. Anscombe amplitude square
    ((anscombeAmplitude x) ^ 2 = x) ∧
    -- 2. Wootters differential isometry
    (4 * (amplitudeDifferential x) ^ 2 = fisherDensity x) ∧
    -- 3. Madelung rotor unimodularity
    (Complex.normSq (madelungRotor x gamma) = 1) ∧
    -- 4. Critical mode norm reconstruction
    (Complex.normSq (criticalMadelungWave x gamma) = x) ∧
    -- 5. Amplitude-rotor factorization
    (criticalMadelungWave x gamma = (anscombeAmplitude x : ℂ) * madelungRotor x gamma) ∧
    -- 6. Fisher distance metric space properties
    (0 ≤ fisherGeodesicDistance x₁ x₂) ∧
    (fisherGeodesicDistance x₁ x₂ = fisherGeodesicDistance x₂ x₁) ∧
    (fisherGeodesicDistance x₁ x₂ = 0 ↔ x₁ = x₂) ∧
    (fisherGeodesicDistance x₁ x₂ + fisherGeodesicDistance x₂ x₃ = fisherGeodesicDistance x₁ x₃) :=
  ⟨anscombe_amplitude_sq (le_of_lt hx),
   wootters_isometry_identity hx,
   madelungRotor_normSq x gamma,
   criticalMadelungWave_normSq x gamma (le_of_lt hx),
   criticalMadelungWave_eq_amplitude_mul_rotor x gamma,
   fisherGeodesicDistance_nonneg x₁ x₂,
   fisherGeodesicDistance_comm x₁ x₂,
   fisherGeodesicDistance_eq_zero_iff h1 h2,
   fisherGeodesicDistance_collinear h23 h34⟩

end InfoGeometry.Canonical.FisherWoottersExtended
