import InfoGeometry.Analysis.BipolarLogDifferential
import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic

/-!
# Bipolar logarithmic integration on native paths

The coefficient owner is `dlog01`. Here it is interpreted by the native
continuous-linear multiplication map and integrated on Mathlib's `Path`.
The endpoint theorem requires a single admissible logarithm branch along
the path. It does not assert that arbitrary closed paths admit such a branch.
-/

noncomputable section

namespace InfoGeometry.Analysis.BipolarCurveIntegral

open Complex Set MeasureTheory
open InfoGeometry.Analysis.BipolarCrossRatioLog
open InfoGeometry.Analysis.BipolarLogDifferential

/-- On a path contained in the principal logarithm chart, integration of
`dq/q` recovers the difference of the logarithm at its endpoints. -/
theorem curveIntegral_dlog01_eq_log_sub {a b : ℂ} (γ : Path a b)
    (hpunct : ∀ t ∈ Icc (0 : ℝ) 1, γ.extend t ∈ punctured01)
    (hslit : ∀ t ∈ Icc (0 : ℝ) 1, crossRatio01 (γ.extend t) ∈ slitPlane)
    (hγ : ∀ t ∈ Ioo (0 : ℝ) 1, DifferentiableAt ℝ γ.extend t)
    (hint : IntervalIntegrable
      (fun t => dlog01 (γ.extend t) * deriv γ.extend t) volume 0 1) :
    curveIntegral (fun z => ContinuousLinearMap.mul ℂ ℂ (dlog01 z)) γ =
      bipolarLog b - bipolarLog a := by
  rw [curveIntegral_eq_intervalIntegral_deriv]
  have hcont : ContinuousOn (fun t => bipolarLog (γ.extend t)) (Icc (0 : ℝ) 1) := by
    intro t ht
    exact ((hasDerivAt_bipolarLog (hpunct t ht) (hslit t ht)).continuousAt.comp
      γ.extend.continuous.continuousAt).continuousWithinAt
  have hderiv : ∀ t ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (fun u => bipolarLog (γ.extend u))
        (dlog01 (γ.extend t) * deriv γ.extend t) t := by
    intro t ht
    exact (hasDerivAt_bipolarLog (hpunct t ⟨ht.1.le, ht.2.le⟩)
      (hslit t ⟨ht.1.le, ht.2.le⟩)).comp t (hγ t ht).hasDerivAt
  simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (by norm_num : (0 : ℝ) ≤ 1) hcont hderiv hint

/-- The exponential of the genuine path integral is the endpoint quotient
of the existing Möbius coordinate, whenever the preceding branch conditions hold. -/
theorem exp_curveIntegral_dlog01_eq_ratio {a b : ℂ} (γ : Path a b)
    (hpunct : ∀ t ∈ Icc (0 : ℝ) 1, γ.extend t ∈ punctured01)
    (hslit : ∀ t ∈ Icc (0 : ℝ) 1, crossRatio01 (γ.extend t) ∈ slitPlane)
    (hγ : ∀ t ∈ Ioo (0 : ℝ) 1, DifferentiableAt ℝ γ.extend t)
    (hint : IntervalIntegrable
      (fun t => dlog01 (γ.extend t) * deriv γ.extend t) volume 0 1) :
    exp (curveIntegral (fun z => ContinuousLinearMap.mul ℂ ℂ (dlog01 z)) γ) =
      crossRatio01 b / crossRatio01 a := by
  rw [curveIntegral_dlog01_eq_log_sub γ hpunct hslit hγ hint, exp_sub]
  have ha : a ∈ punctured01 := by simpa using hpunct 0 (by norm_num)
  have hb : b ∈ punctured01 := by simpa using hpunct 1 (by norm_num)
  rw [exp_bipolarLog hb, exp_bipolarLog ha]

/-! ### Closed admissible paths

The preceding endpoint formula immediately gives the exact local statement for
a closed path which remains in one logarithm chart.  This is deliberately
conditional: a path winding around a puncture need not admit such a global
branch, and its nonzero period belongs to the separate contour/monodromy
owners.
-/

theorem curveIntegral_dlog01_eq_zero_of_loop {a : ℂ} (γ : Path a a)
    (hpunct : ∀ t ∈ Icc (0 : ℝ) 1, γ.extend t ∈ punctured01)
    (hslit : ∀ t ∈ Icc (0 : ℝ) 1,
      crossRatio01 (γ.extend t) ∈ slitPlane)
    (hγ : ∀ t ∈ Ioo (0 : ℝ) 1, DifferentiableAt ℝ γ.extend t)
    (hint : IntervalIntegrable
      (fun t => dlog01 (γ.extend t) * deriv γ.extend t) volume 0 1) :
    curveIntegral (fun z => ContinuousLinearMap.mul ℂ ℂ (dlog01 z)) γ = 0 := by
  rw [curveIntegral_dlog01_eq_log_sub γ hpunct hslit hγ hint]
  simp

theorem exp_curveIntegral_dlog01_eq_one_of_loop {a : ℂ} (γ : Path a a)
    (hpunct : ∀ t ∈ Icc (0 : ℝ) 1, γ.extend t ∈ punctured01)
    (hslit : ∀ t ∈ Icc (0 : ℝ) 1,
      crossRatio01 (γ.extend t) ∈ slitPlane)
    (hγ : ∀ t ∈ Ioo (0 : ℝ) 1, DifferentiableAt ℝ γ.extend t)
    (hint : IntervalIntegrable
      (fun t => dlog01 (γ.extend t) * deriv γ.extend t) volume 0 1) :
    Complex.exp
        (curveIntegral (fun z => ContinuousLinearMap.mul ℂ ℂ (dlog01 z)) γ) = 1 := by
  rw [curveIntegral_dlog01_eq_zero_of_loop γ hpunct hslit hγ hint]
  exact Complex.exp_zero

/-! ### Branch-free holonomy laws

The exponential of the curve integral is defined without choosing a logarithm
branch.  Consequently its concatenation and reversal laws require only the
native curve-integrability hypotheses.
-/

theorem exp_curveIntegral_dlog01_trans_mul {a b c : ℂ}
    (γ : Path a b) (δ : Path b c)
    (hcurveγ : CurveIntegrable
      (fun z => ContinuousLinearMap.mul ℂ ℂ (dlog01 z)) γ)
    (hcurveδ : CurveIntegrable
      (fun z => ContinuousLinearMap.mul ℂ ℂ (dlog01 z)) δ) :
    Complex.exp
        (curveIntegral (fun z => ContinuousLinearMap.mul ℂ ℂ (dlog01 z))
          (γ.trans δ)) =
      Complex.exp
          (curveIntegral (fun z => ContinuousLinearMap.mul ℂ ℂ (dlog01 z)) γ) *
        Complex.exp
          (curveIntegral (fun z => ContinuousLinearMap.mul ℂ ℂ (dlog01 z)) δ) := by
  rw [curveIntegral_trans hcurveγ hcurveδ, Complex.exp_add]

theorem exp_curveIntegral_dlog01_symm_inv {a b : ℂ} (γ : Path a b)
    :
    Complex.exp
        (curveIntegral (fun z => ContinuousLinearMap.mul ℂ ℂ (dlog01 z)) γ.symm) =
      (Complex.exp
        (curveIntegral (fun z => ContinuousLinearMap.mul ℂ ℂ (dlog01 z)) γ))⁻¹ := by
  rw [curveIntegral_symm, Complex.exp_neg]

/-- Endpoint recovery is compatible with concatenation of admissible paths.
The explicit `CurveIntegrable` hypotheses are the native hypotheses required by
Mathlib's concatenation theorem; the remaining hypotheses supply the endpoint
formula on each leg. -/
theorem curveIntegral_dlog01_trans_eq_log_sub {a b c : ℂ}
    (γ : Path a b) (δ : Path b c)
    (hcurveγ : CurveIntegrable
      (fun z => ContinuousLinearMap.mul ℂ ℂ (dlog01 z)) γ)
    (hcurveδ : CurveIntegrable
      (fun z => ContinuousLinearMap.mul ℂ ℂ (dlog01 z)) δ)
    (hpunctγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.extend t ∈ punctured01)
    (hslitγ : ∀ t ∈ Icc (0 : ℝ) 1,
      crossRatio01 (γ.extend t) ∈ slitPlane)
    (hγ : ∀ t ∈ Ioo (0 : ℝ) 1, DifferentiableAt ℝ γ.extend t)
    (hintγ : IntervalIntegrable
      (fun t => dlog01 (γ.extend t) * deriv γ.extend t) volume 0 1)
    (hpunctδ : ∀ t ∈ Icc (0 : ℝ) 1, δ.extend t ∈ punctured01)
    (hslitδ : ∀ t ∈ Icc (0 : ℝ) 1,
      crossRatio01 (δ.extend t) ∈ slitPlane)
    (hδ : ∀ t ∈ Ioo (0 : ℝ) 1, DifferentiableAt ℝ δ.extend t)
    (hintδ : IntervalIntegrable
      (fun t => dlog01 (δ.extend t) * deriv δ.extend t) volume 0 1) :
    curveIntegral (fun z => ContinuousLinearMap.mul ℂ ℂ (dlog01 z))
        (γ.trans δ) = bipolarLog c - bipolarLog a := by
  rw [curveIntegral_trans hcurveγ hcurveδ]
  rw [curveIntegral_dlog01_eq_log_sub γ hpunctγ hslitγ hγ hintγ,
    curveIntegral_dlog01_eq_log_sub δ hpunctδ hslitδ hδ hintδ]
  ring

/-- The exponential endpoint quotient is likewise invariant under splitting a
path into two admissible legs. -/
theorem exp_curveIntegral_dlog01_trans_eq_ratio {a b c : ℂ}
    (γ : Path a b) (δ : Path b c)
    (hcurveγ : CurveIntegrable
      (fun z => ContinuousLinearMap.mul ℂ ℂ (dlog01 z)) γ)
    (hcurveδ : CurveIntegrable
      (fun z => ContinuousLinearMap.mul ℂ ℂ (dlog01 z)) δ)
    (hpunctγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.extend t ∈ punctured01)
    (hslitγ : ∀ t ∈ Icc (0 : ℝ) 1,
      crossRatio01 (γ.extend t) ∈ slitPlane)
    (hγ : ∀ t ∈ Ioo (0 : ℝ) 1, DifferentiableAt ℝ γ.extend t)
    (hintγ : IntervalIntegrable
      (fun t => dlog01 (γ.extend t) * deriv γ.extend t) volume 0 1)
    (hpunctδ : ∀ t ∈ Icc (0 : ℝ) 1, δ.extend t ∈ punctured01)
    (hslitδ : ∀ t ∈ Icc (0 : ℝ) 1,
      crossRatio01 (δ.extend t) ∈ slitPlane)
    (hδ : ∀ t ∈ Ioo (0 : ℝ) 1, DifferentiableAt ℝ δ.extend t)
    (hintδ : IntervalIntegrable
      (fun t => dlog01 (δ.extend t) * deriv δ.extend t) volume 0 1) :
    exp (curveIntegral (fun z => ContinuousLinearMap.mul ℂ ℂ (dlog01 z))
        (γ.trans δ)) = crossRatio01 c / crossRatio01 a := by
  rw [curveIntegral_dlog01_trans_eq_log_sub γ δ hcurveγ hcurveδ
    hpunctγ hslitγ hγ hintγ hpunctδ hslitδ hδ hintδ, exp_sub]
  have ha : a ∈ punctured01 := by simpa using hpunctγ 0 (by norm_num)
  have hc : c ∈ punctured01 := by simpa using hpunctδ 1 (by norm_num)
  rw [exp_bipolarLog hc, exp_bipolarLog ha]

end InfoGeometry.Analysis.BipolarCurveIntegral
