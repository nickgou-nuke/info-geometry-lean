import InfoGeometry.Convex.Bregman
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.Convex.Deriv

/-!
# Convex Duality (1D Structural Layer)

Minimal structural interface used to express Fenchel gaps, Bregman divergence,
and parameter-space KL/Bregman identities.
-/

namespace InfoGeometry.ConvexDuality

/-- Fenchel gap for a primal/dual pair. -/
def fenchelGap (f fStar : ℝ → ℝ) (θ η : ℝ) : ℝ :=
  f θ + fStar η - η * θ

/-- Parameterized KL in exponential-family sign convention. -/
noncomputable def KL_param (A : ℝ → ℝ) (θ θ' : ℝ) : ℝ :=
  InfoGeometry.bregmanDiv A θ' θ

lemma KL_param_eq_bregman_swap (A : ℝ → ℝ) (θ θ' : ℝ) :
    KL_param A θ θ' = InfoGeometry.bregmanDiv A θ' θ := by
  rfl

lemma KL_param_expanded (A : ℝ → ℝ) (θ θ' : ℝ) :
    KL_param A θ θ'
      =
    A θ' - A θ - deriv A θ * (θ' - θ) := by
  unfold KL_param InfoGeometry.bregmanDiv
  ring

/-- Nonnegativity of Bregman divergence from convexity and differentiability at the basepoint. -/
lemma bregman_nonneg_of_convex_at
    {f : ℝ → ℝ}
    (hconv : ConvexOn ℝ Set.univ f)
    (θ θ' : ℝ)
    (hfd' : DifferentiableAt ℝ f θ') :
    0 ≤ InfoGeometry.bregmanDiv f θ θ' := by
  unfold InfoGeometry.bregmanDiv
  by_cases hlt : θ' < θ
  · have hslope : deriv f θ' ≤ slope f θ' θ := by
      exact hconv.deriv_le_slope (by simp) (by simp) hlt hfd'
    have hmul : deriv f θ' * (θ - θ') ≤ f θ - f θ' := by
      have hmul' := mul_le_mul_of_nonneg_right hslope (sub_nonneg.mpr hlt.le)
      have hden : θ - θ' ≠ 0 := sub_ne_zero.mpr hlt.ne'
      calc
        deriv f θ' * (θ - θ') ≤ slope f θ' θ * (θ - θ') := hmul'
        _ = ((f θ - f θ') / (θ - θ')) * (θ - θ') := by
              rw [slope_def_field]
        _ = f θ - f θ' := by
              field_simp [hden]
    exact sub_nonneg.mpr hmul
  · by_cases hEq : θ = θ'
    · simp [hEq]
    · have hlt' : θ < θ' := lt_of_le_of_ne (le_of_not_gt hlt) hEq
      have hslope : slope f θ θ' ≤ deriv f θ' := by
        exact hconv.slope_le_deriv (by simp) (by simp) hlt' hfd'
      have hmul : f θ' - f θ ≤ deriv f θ' * (θ' - θ) := by
        have hmul' := mul_le_mul_of_nonneg_right hslope (sub_nonneg.mpr hlt'.le)
        have hden : θ' - θ ≠ 0 := sub_ne_zero.mpr hlt'.ne'
        calc
          f θ' - f θ = slope f θ θ' * (θ' - θ) := by
            rw [slope_def_field]
            field_simp [hden]
          _ ≤ deriv f θ' * (θ' - θ) := hmul'
      have hgoal : 0 ≤ deriv f θ' * (θ' - θ) - (f θ' - f θ) :=
        sub_nonneg.mpr hmul
      have hring' :
          deriv f θ' * (θ' - θ) - (f θ' - f θ)
            = f θ - f θ' - deriv f θ' * (θ - θ') := by
        ring
      exact hring' ▸ hgoal

/-- Backward-compatible stronger form assuming global differentiability. -/
lemma bregman_nonneg_of_convex
    {f : ℝ → ℝ}
    (hconv : ConvexOn ℝ Set.univ f)
    (hfd : Differentiable ℝ f)
    (θ θ' : ℝ) :
    0 ≤ InfoGeometry.bregmanDiv f θ θ' :=
  bregman_nonneg_of_convex_at (hconv := hconv) θ θ' (hfd θ')

/-- Nonnegativity of parameter-space KL in Bregman form, assuming differentiability at `θ`. -/
lemma KL_param_nonneg_of_convex_at
    {A : ℝ → ℝ}
    (hconv : ConvexOn ℝ Set.univ A)
    (θ θ' : ℝ)
    (hfd : DifferentiableAt ℝ A θ) :
    0 ≤ KL_param A θ θ' := by
  simpa [KL_param] using bregman_nonneg_of_convex_at (hconv := hconv) θ' θ hfd

/-- Nonnegativity of parameter-space KL in Bregman form. -/
lemma KL_param_nonneg_of_convex
    {A : ℝ → ℝ}
    (hconv : ConvexOn ℝ Set.univ A)
    (hfd : Differentiable ℝ A)
    (θ θ' : ℝ) :
    0 ≤ KL_param A θ θ' := by
  exact KL_param_nonneg_of_convex_at (hconv := hconv) θ θ' (hfd θ)

end InfoGeometry.ConvexDuality
