import InfoGeometry.Analysis.BipolarLoopWindingCarrier
import InfoGeometry.Analysis.BipolarLoopWindingPeriod
import InfoGeometry.Analysis.BipolarLogLiftDerivativeBridge

/-!
# Covering endpoint readout and contour period

This file connects the two native endpoint integers supplied by the
exponential covering to the existing interval-integral reduction theorem.
The regularity and derivative equations for the two logarithmic lifts remain
explicit hypotheses.  Thus this bridge does not define winding by an
integral, and it does not claim the still-missing classification of arbitrary
loops by `WindingPair`.
-/

noncomputable section

namespace InfoGeometry.Analysis.BipolarLoopWindingPeriodCarrierBridge

open Complex Set MeasureTheory
open InfoGeometry.Analysis.BipolarAdmissibleLoops
open InfoGeometry.Analysis.BipolarCrossRatioLog
open InfoGeometry.Analysis.BipolarLoopWindingCarrier
open InfoGeometry.Analysis.BipolarLoopWindingPeriod
open InfoGeometry.Analysis.BipolarLogLiftDerivativeBridge
open InfoGeometry.Analysis.BipolarWindingPeriodLattice

abbrev Period := 2 * (Real.pi : ℂ) * Complex.I

theorem integral_eq_circulationPeriod_of_log_lifts
    (γ : AdmissibleLoop)
    (W₀ W₁ : ℝ → ℂ)
    (hcont₀ : ContinuousOn W₀ (Icc (0 : ℝ) 1))
    (hcont₁ : ContinuousOn W₁ (Icc (0 : ℝ) 1))
    (hderiv₀ : ∀ t ∈ Ioo (0 : ℝ) 1,
      HasDerivAt W₀
        ((γ.path.extend t)⁻¹ * deriv γ.path.extend t) t)
    (hderiv₁ : ∀ t ∈ Ioo (0 : ℝ) 1,
      HasDerivAt W₁
        ((γ.path.extend t - 1)⁻¹ * deriv γ.path.extend t) t)
    (hint₀ : IntervalIntegrable
      (fun t => (γ.path.extend t)⁻¹ * deriv γ.path.extend t)
      volume 0 1)
    (hint₁ : IntervalIntegrable
      (fun t => (γ.path.extend t - 1)⁻¹ * deriv γ.path.extend t)
      volume 0 1)
    (hend₀ : W₀ 1 = W₀ 0 +
      (bipolarLiftEndpointPair γ).1 * Period)
    (hend₁ : W₁ 1 = W₁ 0 +
      (bipolarLiftEndpointPair γ).2 * Period) :
    integral γ = circulationPeriod (bipolarLiftEndpointPair γ) := by
  have hperiod := integral_eq_period_difference_of_log_lifts γ W₀ W₁
    (bipolarLiftEndpointPair γ).1 (bipolarLiftEndpointPair γ).2
    hcont₀ hcont₁ hderiv₀ hderiv₁ hint₀ hint₁ hend₀ hend₁
  rw [hperiod]
  simp [circulationPeriod, residueWinding]

/-! ### Holonomy readout from the genuine period value

This is deliberately downstream of the contour-period theorem: it does not
define a period by declaring the holonomy to be trivial. -/

theorem holonomy_eq_one_of_circulationPeriod
    (γ : AdmissibleLoop) (w : WindingPair)
    (hperiod : integral γ = circulationPeriod w) :
    holonomy γ = 1 := by
  rw [holonomy, hperiod, circulationPeriod]
  rcases w with ⟨m, n⟩
  have h := Complex.exp_int_mul_two_pi_mul_I (m - n)
  simpa [residueWinding, mul_assoc, mul_comm, mul_left_comm] using h

/-! ### Native-lift endpoint specialization

The endpoint equations are supplied by the actual native exponential lifts;
the differentiability and interval-integrability hypotheses remain explicit
analytic obligations. -/

theorem integral_eq_circulationPeriod_of_native_lifts
    (γ : AdmissibleLoop)
    (W₀ W₁ : ℝ → ℂ)
    (hW₀ : ∀ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1),
      W₀ t = nativeCrossRatioLift γ ⟨t, ht.1, ht.2⟩)
    (hW₁ : ∀ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1),
      W₁ t = nativeShiftedLift γ ⟨t, ht.1, ht.2⟩)
    (hcont₀ : ContinuousOn W₀ (Icc (0 : ℝ) 1))
    (hcont₁ : ContinuousOn W₁ (Icc (0 : ℝ) 1))
    (hderiv₀ : ∀ t ∈ Ioo (0 : ℝ) 1,
      HasDerivAt W₀
        ((γ.path.extend t)⁻¹ * deriv γ.path.extend t) t)
    (hderiv₁ : ∀ t ∈ Ioo (0 : ℝ) 1,
      HasDerivAt W₁
        ((γ.path.extend t - 1)⁻¹ * deriv γ.path.extend t) t)
    (hint₀ : IntervalIntegrable
      (fun t => (γ.path.extend t)⁻¹ * deriv γ.path.extend t)
      volume 0 1)
    (hint₁ : IntervalIntegrable
      (fun t => (γ.path.extend t - 1)⁻¹ * deriv γ.path.extend t)
      volume 0 1) :
    integral γ = circulationPeriod (bipolarLiftEndpointPair γ) := by
  have hendpoint₀ : W₀ 1 = W₀ 0 +
      (bipolarLiftEndpointPair γ).1 * Period := by
    calc
      W₀ 1 = nativeCrossRatioLift γ 1 := by
        simpa using hW₀ 1 (by norm_num)
      _ = bipolarLog γ.base +
          (bipolarLiftEndpointPair γ).1 * Period := by
        simpa [nativeCrossRatioLift] using
          (bipolarLiftEndpointPair_crossRatio_spec γ)
      _ = W₀ 0 + (bipolarLiftEndpointPair γ).1 * Period := by
        have hzero : W₀ 0 = bipolarLog γ.base := by
          calc
            W₀ 0 = nativeCrossRatioLift γ 0 := by
              simpa using hW₀ 0 (by norm_num)
            _ = bipolarLog γ.base := nativeCrossRatioLift_zero γ
        rw [hzero]
  have hendpoint₁ : W₁ 1 = W₁ 0 +
      (bipolarLiftEndpointPair γ).2 * Period := by
    calc
      W₁ 1 = nativeShiftedLift γ 1 := by
        simpa using hW₁ 1 (by norm_num)
      _ = Complex.log (γ.base - 1) +
          (bipolarLiftEndpointPair γ).2 * Period := by
        simpa [nativeShiftedLift] using
          (bipolarLiftEndpointPair_shifted_spec γ)
      _ = W₁ 0 + (bipolarLiftEndpointPair γ).2 * Period := by
        have hzero : W₁ 0 = Complex.log (γ.base - 1) := by
          calc
            W₁ 0 = nativeShiftedLift γ 0 := by
              simpa using hW₁ 0 (by norm_num)
            _ = Complex.log (γ.base - 1) := nativeShiftedLift_zero γ
        rw [hzero]
  exact integral_eq_circulationPeriod_of_log_lifts γ W₀ W₁
    hcont₀ hcont₁ hderiv₀ hderiv₁ hint₀ hint₁ hendpoint₀ hendpoint₁

/-- The native-lift period law with its derivative equations discharged by the
chain rule.  The path differentiability and integrability hypotheses remain
explicit analytic obligations. -/
theorem integral_eq_circulationPeriod_of_differentiable_native_lifts
    (γ : AdmissibleLoop)
    (W₀ W₁ : ℝ → ℂ)
    (hW₀ : ∀ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1),
      W₀ t = nativeCrossRatioLift γ ⟨t, ht.1, ht.2⟩)
    (hW₁ : ∀ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1),
      W₁ t = nativeShiftedLift γ ⟨t, ht.1, ht.2⟩)
    (hcont₀ : ContinuousOn W₀ (Icc (0 : ℝ) 1))
    (hcont₁ : ContinuousOn W₁ (Icc (0 : ℝ) 1))
    (hEq₀ : ∀ t ∈ Ioo (0 : ℝ) 1,
      Complex.exp (W₀ t) = γ.path.extend t)
    (hEq₁ : ∀ t ∈ Ioo (0 : ℝ) 1,
      Complex.exp (W₁ t) = γ.path.extend t - 1)
    (hpath : ∀ t ∈ Ioo (0 : ℝ) 1,
      DifferentiableAt ℝ γ.path.extend t)
    (hW₀diff : ∀ t ∈ Ioo (0 : ℝ) 1, DifferentiableAt ℝ W₀ t)
    (hW₁diff : ∀ t ∈ Ioo (0 : ℝ) 1, DifferentiableAt ℝ W₁ t)
    (hint₀ : IntervalIntegrable
      (fun t => (γ.path.extend t)⁻¹ * deriv γ.path.extend t)
      volume 0 1)
    (hint₁ : IntervalIntegrable
      (fun t => (γ.path.extend t - 1)⁻¹ * deriv γ.path.extend t)
      volume 0 1) :
    integral γ = circulationPeriod (bipolarLiftEndpointPair γ) := by
  have hendpoint₀ : W₀ 1 = W₀ 0 +
      (bipolarLiftEndpointPair γ).1 * Period := by
    calc
      W₀ 1 = nativeCrossRatioLift γ 1 := by
        simpa using hW₀ 1 (by norm_num)
      _ = bipolarLog γ.base +
          (bipolarLiftEndpointPair γ).1 * Period := by
        simpa [nativeCrossRatioLift] using
          (bipolarLiftEndpointPair_crossRatio_spec γ)
      _ = W₀ 0 + (bipolarLiftEndpointPair γ).1 * Period := by
        have hzero : W₀ 0 = bipolarLog γ.base := by
          calc
            W₀ 0 = nativeCrossRatioLift γ 0 := by
              simpa using hW₀ 0 (by norm_num)
            _ = bipolarLog γ.base := nativeCrossRatioLift_zero γ
        rw [hzero]
  have hendpoint₁ : W₁ 1 = W₁ 0 +
      (bipolarLiftEndpointPair γ).2 * Period := by
    calc
      W₁ 1 = nativeShiftedLift γ 1 := by
        simpa using hW₁ 1 (by norm_num)
      _ = Complex.log (γ.base - 1) +
          (bipolarLiftEndpointPair γ).2 * Period := by
        simpa [nativeShiftedLift] using
          (bipolarLiftEndpointPair_shifted_spec γ)
      _ = W₁ 0 + (bipolarLiftEndpointPair γ).2 * Period := by
        have hzero : W₁ 0 = Complex.log (γ.base - 1) := by
          calc
            W₁ 0 = nativeShiftedLift γ 0 := by
              simpa using hW₁ 0 (by norm_num)
            _ = Complex.log (γ.base - 1) := nativeShiftedLift_zero γ
        rw [hzero]
  have hperiod := integral_eq_period_difference_of_differentiable_exp_lifts γ W₀ W₁
    (bipolarLiftEndpointPair γ).1 (bipolarLiftEndpointPair γ).2
    hcont₀ hcont₁ hEq₀ hEq₁ hpath hW₀diff hW₁diff hint₀ hint₁
    hendpoint₀ hendpoint₁
  simpa [circulationPeriod, residueWinding] using hperiod

end InfoGeometry.Analysis.BipolarLoopWindingPeriodCarrierBridge
