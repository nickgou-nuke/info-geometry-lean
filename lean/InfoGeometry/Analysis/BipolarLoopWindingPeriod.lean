import InfoGeometry.Analysis.BipolarAdmissibleLoops
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Analysis.BipolarWindingPeriodLattice

/-!
# Piecewise-`C¹` loop period reduction for the bipolar logarithmic form

This file advances the arbitrary-loop frontier without identifying a winding
number with the integral being computed.  A loop is the repository-owned
`AdmissibleLoop`; the two displayed logarithmic lifts are explicit analytic
data.  From their derivative equations and endpoint deck translations, the
period formula follows by the interval fundamental theorem of calculus.

The remaining topological theorem is precisely the existence of such lifts for
every admissible piecewise-`C¹` loop and the identification of their integers
with the two standard winding numbers.
-/

noncomputable section

namespace InfoGeometry.Analysis.BipolarLoopWindingPeriod

open Complex Set MeasureTheory
open InfoGeometry.Analysis.BipolarAdmissibleLoops
open InfoGeometry.Analysis.BipolarCrossRatioLog
open InfoGeometry.Analysis.BipolarLogDifferential

abbrev Period := 2 * (Real.pi : ℂ) * Complex.I

/-- The native regularity condition used for a piecewise-`C¹` path segment.
The endpoint values are handled separately by `Path`; only interior
derivatives enter the contour integral. -/
def InteriorC1 (γ : AdmissibleLoop) : Prop :=
  ∀ t ∈ Ioo (0 : ℝ) 1, DifferentiableAt ℝ γ.path.extend t

theorem interiorC1_of_hasDeriv
    (γ : AdmissibleLoop)
    (hγ : ∀ t ∈ Ioo (0 : ℝ) 1,
      HasDerivAt γ.path.extend (deriv γ.path.extend t) t) :
    InteriorC1 γ := by
  intro t ht
  exact (hγ t ht).differentiableAt

theorem curveIntegral_dlog01_eq_intervalIntegral
    (γ : AdmissibleLoop) :
    integral γ = ∫ t in (0 : ℝ)..1,
      dlog01 (γ.path.extend t) * deriv γ.path.extend t := by
  change curveIntegral dlog01Form γ.path = _
  rw [curveIntegral_eq_intervalIntegral_deriv]
  apply intervalIntegral.integral_congr_ae
  filter_upwards with t ht
  rfl

/-- The contour period is computed from two actual logarithmic lifts.  The
lift equations are deliberately hypotheses: the global covering-space proof
that supplies them for every piecewise-`C¹` loop is the next topological node,
not an assumption hidden in a definition of `wind`. -/
theorem integral_eq_period_difference_of_log_lifts
    (γ : AdmissibleLoop)
    (W₀ W₁ : ℝ → ℂ) (n₀ n₁ : ℤ)
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
    (hend₀ : W₀ 1 = W₀ 0 + n₀ * Period)
    (hend₁ : W₁ 1 = W₁ 0 + n₁ * Period) :
    integral γ = (n₀ - n₁) * Period := by
  have hmain := curveIntegral_dlog01_eq_intervalIntegral γ
  have h0 : (∫ t in (0 : ℝ)..1,
      (γ.path.extend t)⁻¹ * deriv γ.path.extend t) = W₀ 1 - W₀ 0 := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      (by norm_num) hcont₀ hderiv₀ hint₀
  have h1 : (∫ t in (0 : ℝ)..1,
      (γ.path.extend t - 1)⁻¹ * deriv γ.path.extend t) = W₁ 1 - W₁ 0 := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      (by norm_num) hcont₁ hderiv₁ hint₁
  rw [hmain]
  have hsplit : ∀ t ∈ uIcc (0 : ℝ) 1,
      dlog01 (γ.path.extend t) * deriv γ.path.extend t =
        (γ.path.extend t)⁻¹ * deriv γ.path.extend t -
          (γ.path.extend t - 1)⁻¹ * deriv γ.path.extend t := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := by
      simpa [uIcc] using ht
    have hmem : γ.path.extend t ∈
        InfoGeometry.Analysis.BipolarCrossRatioLog.punctured01 := by
      rw [γ.path.extend_apply ht']
      change γ.path ⟨t, ht'.1, ht'.2⟩ ∈
        InfoGeometry.Analysis.BipolarCrossRatioLog.punctured01
      exact path_mem_punctured γ
    have h0 : γ.path.extend t ≠ 0 := hmem.1
    have h1 : γ.path.extend t ≠ 1 := hmem.2
    have h1s : 1 - γ.path.extend t ≠ 0 := sub_ne_zero.mpr h1.symm
    have hm1 : γ.path.extend t - 1 ≠ 0 := sub_ne_zero.mpr h1
    rw [dlog01]
    field_simp [h0, h1s, hm1]; ring_nf
  have hrewrite :
      (∫ t in (0 : ℝ)..1,
        dlog01 (γ.path.extend t) * deriv γ.path.extend t) =
        ∫ t in (0 : ℝ)..1,
          ((γ.path.extend t)⁻¹ * deriv γ.path.extend t -
            (γ.path.extend t - 1)⁻¹ * deriv γ.path.extend t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    exact hsplit t ht
  rw [hrewrite, intervalIntegral.integral_sub hint₀ hint₁,
    h0, h1, hend₀, hend₁]
  ring

end InfoGeometry.Analysis.BipolarLoopWindingPeriod
