import InfoGeometry.Analysis.BipolarLoopWindingPeriod
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Topology.Basic

/-!
# Derivatives of logarithmic lifts

If a differentiable lift exponentiates to a nonzero curve, its derivative is
forced by the chain rule.  This is the local analytic edge needed before the
covering lift can be used in the arbitrary-loop period theorem.
-/

noncomputable section

namespace InfoGeometry.Analysis.BipolarLogLiftDerivativeBridge

open Complex Set Filter MeasureTheory
open scoped Topology
open InfoGeometry.Analysis.BipolarAdmissibleLoops
open InfoGeometry.Analysis.BipolarLoopWindingPeriod

theorem hasDerivAt_exp_lift_eq_inv_mul
    {W γ : ℝ → ℂ} {t : ℝ} {w v : ℂ}
    (ht : t ∈ Ioo (0 : ℝ) 1)
    (hEq : ∀ u ∈ Ioo (0 : ℝ) 1, Complex.exp (W u) = γ u)
    (hW : HasDerivAt W w t)
    (hγ : HasDerivAt γ v t) :
    w = (γ t)⁻¹ * v := by
  have hlocal : (fun u => Complex.exp (W u)) =ᶠ[nhds t] γ := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with u hu
    exact hEq u hu
  have hexp : HasDerivAt (fun u => Complex.exp (W u))
      (Complex.exp (W t) * w) t := by
    exact (Complex.hasDerivAt_exp (W t)).comp t hW
  have hexp' : HasDerivAt γ (Complex.exp (W t) * w) t :=
    hexp.congr_of_eventuallyEq hlocal.symm
  have hderiv : Complex.exp (W t) * w = v :=
    hexp'.unique hγ
  have hexp0 : Complex.exp (W t) ≠ 0 := Complex.exp_ne_zero _
  calc
    w = (Complex.exp (W t))⁻¹ * (Complex.exp (W t) * w) := by
      field_simp
    _ = (γ t)⁻¹ * v := by rw [hderiv, hEq t ht]

theorem hasDerivAt_exp_shifted_lift_eq_sub_inv_mul
    {W γ : ℝ → ℂ} {t : ℝ} {w v : ℂ}
    (ht : t ∈ Ioo (0 : ℝ) 1)
    (hEq : ∀ u ∈ Ioo (0 : ℝ) 1, Complex.exp (W u) = γ u - 1)
    (hW : HasDerivAt W w t)
    (hγ : HasDerivAt γ v t) :
    w = (γ t - 1)⁻¹ * v := by
  have hγ' : HasDerivAt (fun u => γ u - 1) v t := by
    simpa using hγ.sub_const 1
  have h := hasDerivAt_exp_lift_eq_inv_mul ht
    hEq hW hγ'
  simpa using h

/-! The chain-rule lemmas discharge the derivative premises of the existing
period reduction.  The endpoint translations remain explicit because they are
the genuine deck data supplied by the exponential covering. -/

theorem integral_eq_period_difference_of_differentiable_exp_lifts
    (γ : AdmissibleLoop)
    (W₀ W₁ : ℝ → ℂ) (n₀ n₁ : ℤ)
    (hcont₀ : ContinuousOn W₀ (Icc (0 : ℝ) 1))
    (hcont₁ : ContinuousOn W₁ (Icc (0 : ℝ) 1))
    (hEq₀ : ∀ t ∈ Ioo (0 : ℝ) 1,
      Complex.exp (W₀ t) = γ.path.extend t)
    (hEq₁ : ∀ t ∈ Ioo (0 : ℝ) 1,
      Complex.exp (W₁ t) = γ.path.extend t - 1)
    (hpath : ∀ t ∈ Ioo (0 : ℝ) 1,
      DifferentiableAt ℝ γ.path.extend t)
    (hW₀ : ∀ t ∈ Ioo (0 : ℝ) 1, DifferentiableAt ℝ W₀ t)
    (hW₁ : ∀ t ∈ Ioo (0 : ℝ) 1, DifferentiableAt ℝ W₁ t)
    (hint₀ : IntervalIntegrable
      (fun t => (γ.path.extend t)⁻¹ * deriv γ.path.extend t)
      volume 0 1)
    (hint₁ : IntervalIntegrable
      (fun t => (γ.path.extend t - 1)⁻¹ * deriv γ.path.extend t)
      volume 0 1)
    (hend₀ : W₀ 1 = W₀ 0 + n₀ * Period)
    (hend₁ : W₁ 1 = W₁ 0 + n₁ * Period) :
    integral γ = (n₀ - n₁) * Period := by
  apply integral_eq_period_difference_of_log_lifts γ W₀ W₁ n₀ n₁
    hcont₀ hcont₁
  · intro t ht
    have h := hasDerivAt_exp_lift_eq_inv_mul ht hEq₀
      (hW₀ t ht).hasDerivAt (hpath t ht).hasDerivAt
    convert (hW₀ t ht).hasDerivAt using 1
    exact h.symm
  · intro t ht
    have h := hasDerivAt_exp_shifted_lift_eq_sub_inv_mul ht hEq₁
      (hW₁ t ht).hasDerivAt (hpath t ht).hasDerivAt
    convert (hW₁ t ht).hasDerivAt using 1
    exact h.symm
  · exact hint₀
  · exact hint₁
  · exact hend₀
  · exact hend₁

end InfoGeometry.Analysis.BipolarLogLiftDerivativeBridge
