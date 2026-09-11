import InfoGeometry.Arithmetic.MobiusFourierPaperReadout
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Arithmetic.TrigonometricPolynomialLocalMomentBound
import InfoGeometry.Arithmetic.LocalMomentToPointValue

noncomputable section

open scoped BigOperators
open scoped ArithmeticFunction.Moebius
open MeasureTheory

namespace InfoGeometry.Arithmetic.MobiusFourierTrigonometricBridge

open InfoGeometry.Arithmetic.MobiusFourierPaperReadout
open InfoGeometry.Arithmetic.MobiusFourierLocalMoment
open InfoGeometry.Arithmetic.TrigonometricPolynomialLocalMomentBound
open InfoGeometry.Arithmetic.LocalMomentToPointValue

/-- Coefficients of the finite Möbius Fourier sum, extended by zero at the
frequencies outside `1, ..., N`. -/
def mobiusFourierCoefficients (N : ℕ) (n : ℕ) : ℂ :=
  if n ∈ Finset.Icc 1 N then (ArithmeticFunction.moebius n : ℂ) else 0

theorem finiteTrigonometricPolynomial_mobiusFourierSum
    (N : ℕ) (t : ℝ) :
    finiteTrigonometricPolynomial N (mobiusFourierCoefficients N) t =
      mobiusFourierSum N t := by
  classical
  unfold finiteTrigonometricPolynomial mobiusFourierCoefficients mobiusFourierSum
  simp_rw [ite_mul]
  simp only [zero_mul]
  rw [← Finset.sum_filter]
  congr 1
  ext n
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
  omega

theorem mobiusFourierCoefficients_norm_le_one (N n : ℕ) :
    ‖mobiusFourierCoefficients N n‖ ≤ 1 := by
  by_cases h : n ∈ Finset.Icc 1 N
  · simp [mobiusFourierCoefficients, h]
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))
  · simp [mobiusFourierCoefficients, h]

theorem mobiusFourierSum_pointwise_persistence
    (N : ℕ) (t : ℝ) :
    ‖mobiusFourierSum N t - mobiusFourierSum N 0‖ ≤
      (derivativeBound N : ℝ) * |t| := by
  have h := finiteTrigonometricPolynomial_pointwise_persistence
    N (mobiusFourierCoefficients N) t
    (fun n hn => mobiusFourierCoefficients_norm_le_one N n)
  rw [finiteTrigonometricPolynomial_mobiusFourierSum N t,
    finiteTrigonometricPolynomial_mobiusFourierSum N 0] at h
  exact h

/- The deterministic half-value interval following from pointwise
    Lipschitz persistence.  The strict positivity hypothesis keeps the
    division domain explicit; no asymptotic statement is used. -/
/- The deterministic half-value interval following from pointwise Lipschitz persistence. -/
theorem mobiusFourierSum_half_persistence
    (N : ℕ) (t : ℝ)
    (hD : 0 < (derivativeBound N : ℝ))
    (ht : |t| ≤
      ‖mobiusFourierSum N 0‖ / (2 * (derivativeBound N : ℝ))) :
    ‖mobiusFourierSum N 0‖ / 2 ≤
      ‖mobiusFourierSum N t‖ := by
  have hp := mobiusFourierSum_pointwise_persistence N t
  have hmul : (derivativeBound N : ℝ) * |t| ≤
      ‖mobiusFourierSum N 0‖ / 2 := by
    calc
      (derivativeBound N : ℝ) * |t| ≤
          (derivativeBound N : ℝ) *
            (‖mobiusFourierSum N 0‖ /
              (2 * (derivativeBound N : ℝ))) := by
        exact mul_le_mul_of_nonneg_left ht hD.le
      _ = ‖mobiusFourierSum N 0‖ / 2 := by
        field_simp
  have htriangle : ‖mobiusFourierSum N 0‖ ≤
      ‖mobiusFourierSum N t‖ +
        ‖mobiusFourierSum N t - mobiusFourierSum N 0‖ := by
    simpa [sub_sub_cancel] using
      (norm_sub_le (mobiusFourierSum N t)
        (mobiusFourierSum N t - mobiusFourierSum N 0))
  linarith

theorem continuous_mobiusFourierSum (N : ℕ) :
    Continuous (mobiusFourierSum N) := by
  have hfun : mobiusFourierSum N =
      finiteTrigonometricPolynomial N (mobiusFourierCoefficients N) := by
    funext t
    exact (finiteTrigonometricPolynomial_mobiusFourierSum N t).symm
  rw [hfun]
  unfold finiteTrigonometricPolynomial
  fun_prop

theorem mobiusFourierSum_local_moment_lower_bound
    (N q : ℕ) (δ : ℝ)
    (hδ : 0 ≤ δ)
    (hwidth : (derivativeBound N : ℝ) * δ ≤
      ‖mobiusFourierSum N 0‖ / 2) :
    (2 * δ) * (‖mobiusFourierSum N 0‖ / 2) ^ q ≤
      ∫ t in (-δ)..δ, ‖mobiusFourierSum N t‖ ^ q := by
  have hfi : IntervalIntegrable
      (fun t : ℝ => ‖mobiusFourierSum N t‖ ^ q) volume (-δ) δ := by
    exact ((continuous_mobiusFourierSum N).norm.pow q).intervalIntegrable _ _
  have hpoint : ∀ t ∈ Set.Icc (-δ) δ,
      ‖mobiusFourierSum N 0‖ / 2 ≤ ‖mobiusFourierSum N t‖ := by
    intro t ht
    have ht_abs : |t| ≤ δ := by
      rw [abs_le]
      exact ⟨by linarith [ht.1], ht.2⟩
    have hp := mobiusFourierSum_pointwise_persistence N t
    have hC : 0 ≤ (derivativeBound N : ℝ) := by positivity
    have hmul : (derivativeBound N : ℝ) * |t| ≤
        (derivativeBound N : ℝ) * δ :=
      mul_le_mul_of_nonneg_left ht_abs hC
    have htri : ‖mobiusFourierSum N 0‖ ≤
        ‖mobiusFourierSum N t‖ +
          ‖mobiusFourierSum N t - mobiusFourierSum N 0‖ := by
      simpa [sub_sub_cancel] using
        (norm_sub_le (mobiusFourierSum N t)
          (mobiusFourierSum N t - mobiusFourierSum N 0))
    have hsub : ‖mobiusFourierSum N 0‖ -
        (derivativeBound N : ℝ) * δ ≤
        ‖mobiusFourierSum N t‖ := by
      linarith
    linarith
  have hmain := intervalIntegral_norm_pow_lower_bound
    (mobiusFourierSum N) (-δ) δ (‖mobiusFourierSum N 0‖ / 2) q
    (by linarith) hfi (by positivity) hpoint
  convert hmain using 1 <;> ring

theorem mobiusFourierSum_criticalArc_lower_bound
    (N q : ℕ) (c : ℝ) (hN : 0 < N) (hc : 0 ≤ c)
    (hwidth : (derivativeBound N : ℝ) * (c / (N : ℝ)) ≤
      ‖mobiusFourierSum N 0‖ / 2) :
    (2 * (c / (N : ℝ))) * (‖mobiusFourierSum N 0‖ / 2) ^ q ≤
      ∫ t in (-c / (N : ℝ))..(c / (N : ℝ)),
        ‖mobiusFourierSum N t‖ ^ q := by
  have hδ : 0 ≤ c / (N : ℝ) := by positivity
  convert mobiusFourierSum_local_moment_lower_bound N q
    (c / (N : ℝ)) hδ hwidth using 1 <;> ring

theorem localMomentIntegral_criticalArc_lower_bound
    (N q : ℕ) (c : ℝ) (hN : 0 < N) (hc : 0 < c)
    (hwidth : (derivativeBound N : ℝ) * (c / (N : ℝ)) ≤
      ‖mobiusFourierSum N 0‖ / 2) :
    ((N : ℝ) / (2 * c)) * (Real.rpow (N : ℝ) (-1 / 2)) ^ q *
        ((2 * (c / (N : ℝ))) *
          (‖mobiusFourierSum N 0‖ / 2) ^ q) ≤
      localMomentIntegral N q c := by
  rw [localMomentIntegral_eq_scaled_unnormalized]
  have hfactor : 0 ≤
      ((N : ℝ) / (2 * c)) * (Real.rpow (N : ℝ) (-1 / 2)) ^ q := by
    have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
    have hden : 0 ≤ (2 * c) := by positivity
    exact mul_nonneg (div_nonneg hNr.le hden)
      (pow_nonneg (Real.rpow_nonneg hNr.le _) q)
  exact mul_le_mul_of_nonneg_left
    (mobiusFourierSum_criticalArc_lower_bound N q c hN hc.le hwidth)
    hfactor

theorem rootedLocalMoment_criticalArc_lower_bound
    (N q : ℕ) (c : ℝ) (hq : 0 < q) (hN : 0 < N) (hc : 0 < c)
    (hwidth : (derivativeBound N : ℝ) * (c / (N : ℝ)) ≤
      ‖mobiusFourierSum N 0‖ / 2) :
    Real.rpow
        (((N : ℝ) / (2 * c)) * (Real.rpow (N : ℝ) (-1 / 2)) ^ q *
          ((2 * (c / (N : ℝ))) *
            (‖mobiusFourierSum N 0‖ / 2) ^ q))
        (1 / (q : ℝ)) ≤
      rootedLocalMoment N q c hq := by
  unfold rootedLocalMoment
  apply Real.rpow_le_rpow
  · have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
    have hden : 0 < (2 * c) := by positivity
    have h₁ : 0 ≤ (N : ℝ) / (2 * c) := div_nonneg hNr.le hden.le
    have h₂ : 0 ≤ (Real.rpow (N : ℝ) (-1 / 2)) ^ q :=
      pow_nonneg (Real.rpow_nonneg hNr.le _) q
    have h₃ : 0 ≤ (2 * (c / (N : ℝ))) *
        (‖mobiusFourierSum N 0‖ / 2) ^ q := by
      exact mul_nonneg
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (div_nonneg hc.le hNr.le))
        (pow_nonneg (by positivity) q)
    exact mul_nonneg (mul_nonneg h₁ h₂) h₃
  · exact localMomentIntegral_criticalArc_lower_bound N q c hN hc hwidth
  · positivity

end InfoGeometry.Arithmetic.MobiusFourierTrigonometricBridge
