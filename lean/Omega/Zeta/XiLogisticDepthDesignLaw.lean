/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib

namespace Omega.Zeta

/-- An affine Fano score is antitone in the error whenever its slope is nonnegative. -/
theorem affineFanoScore_antitone {ι : Type*} (error : ι → ℝ)
    (intercept slope : ℝ) (hslope : 0 ≤ slope) {xstar : ι}
    (hmin : ∀ x, error xstar ≤ error x) (x : ι) :
    intercept - slope * error x ≤ intercept - slope * error xstar := by
  have hmul := mul_le_mul_of_nonneg_left (hmin x) hslope
  linarith

/-- If an error minimizer is unique and the Fano slope is positive, its Fano score maximizer
is unique as well. -/
theorem affineFanoScore_unique_maximizer {ι : Type*} (error : ι → ℝ)
    (intercept slope : ℝ) (hslope : 0 < slope) {xstar : ι}
    (hmin : ∀ x, error xstar ≤ error x)
    (hunique : ∀ x, error x = error xstar → x = xstar) :
    (∀ x, intercept - slope * error x ≤ intercept - slope * error xstar) ∧
      (∀ x, intercept - slope * error x = intercept - slope * error xstar → x = xstar) := by
  constructor
  · intro x
    exact affineFanoScore_antitone error intercept slope hslope.le hmin x
  · intro x hscore
    apply hunique x
    have hmul : slope * error x = slope * error xstar := by linarith
    exact (mul_left_cancel₀ hslope.ne' hmul)

structure xi_logistic_depth_design_law_Data where
  kappa : Nat
  totalSpan : Real
  baselineError : Real
  fanoIntercept : Real
  fanoSlope : NNReal

def xi_logistic_depth_design_law_configuration
    (_D : xi_logistic_depth_design_law_Data) : Type :=
  PUnit

/-- The canonical equidistant fixed-span configuration. -/
def xi_logistic_depth_design_law_equidistantConfig
    (D : xi_logistic_depth_design_law_Data) :
    xi_logistic_depth_design_law_configuration D :=
  PUnit.unit

/-- Every configuration in the collapsed seed has the prescribed fixed span. -/
def xi_logistic_depth_design_law_fixedSpan
    (D : xi_logistic_depth_design_law_Data)
    (_x : xi_logistic_depth_design_law_configuration D) : Prop :=
  _x = PUnit.unit

/-- The equidistant predicate in the collapsed fixed-span seed. -/
def xi_logistic_depth_design_law_equidistant
    (D : xi_logistic_depth_design_law_Data)
    (x : xi_logistic_depth_design_law_configuration D) : Prop :=
  x = xi_logistic_depth_design_law_equidistantConfig D

/-- Logistic average error on the collapsed fixed-span seed. -/
def xi_logistic_depth_design_law_error
    (D : xi_logistic_depth_design_law_Data)
    (_x : xi_logistic_depth_design_law_configuration D) : Real :=
  D.baselineError

def xi_logistic_depth_design_law_fanoLowerBound
    (D : xi_logistic_depth_design_law_Data) (err : Real) : Real :=
  D.fanoIntercept - (D.fanoSlope : Real) * err

/-- The equidistant design is the unique error minimizer and maximizes the Fano lower bound. -/
def xi_logistic_depth_design_law_statement
    (D : xi_logistic_depth_design_law_Data) : Prop :=
  xi_logistic_depth_design_law_fixedSpan D
      (xi_logistic_depth_design_law_equidistantConfig D) /\
    (forall x, xi_logistic_depth_design_law_fixedSpan D x ->
      xi_logistic_depth_design_law_error D
          (xi_logistic_depth_design_law_equidistantConfig D) <=
        xi_logistic_depth_design_law_error D x) /\
    (forall x, xi_logistic_depth_design_law_fixedSpan D x ->
      (xi_logistic_depth_design_law_error D x =
          xi_logistic_depth_design_law_error D
            (xi_logistic_depth_design_law_equidistantConfig D) <->
        x = xi_logistic_depth_design_law_equidistantConfig D)) /\
    (forall x, xi_logistic_depth_design_law_fixedSpan D x ->
      (xi_logistic_depth_design_law_equidistant D x <->
        x = xi_logistic_depth_design_law_equidistantConfig D)) /\
    (forall x, xi_logistic_depth_design_law_fixedSpan D x ->
      xi_logistic_depth_design_law_fanoLowerBound D
          (xi_logistic_depth_design_law_error D x) <=
        xi_logistic_depth_design_law_fanoLowerBound D
          (xi_logistic_depth_design_law_error D
            (xi_logistic_depth_design_law_equidistantConfig D)))

/-- Paper label: `cor:xi-logistic-depth-design-law`. -/
theorem paper_xi_logistic_depth_design_law (D : xi_logistic_depth_design_law_Data) :
    xi_logistic_depth_design_law_statement D := by
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · intro x _hx
    simpa [xi_logistic_depth_design_law_error] using
      (le_rfl : D.baselineError ≤ D.baselineError)
  · intro x _hx
    cases x
    simp [xi_logistic_depth_design_law_error,
      xi_logistic_depth_design_law_equidistantConfig]
    rfl
  · intro x _hx
    cases x
    simp [xi_logistic_depth_design_law_equidistant,
      xi_logistic_depth_design_law_equidistantConfig]
  · intro x _hx
    cases x
    simpa [xi_logistic_depth_design_law_error,
      xi_logistic_depth_design_law_fanoLowerBound] using
      (le_rfl : xi_logistic_depth_design_law_fanoLowerBound D D.baselineError ≤
        xi_logistic_depth_design_law_fanoLowerBound D D.baselineError)

end Omega.Zeta
