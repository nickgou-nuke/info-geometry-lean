import Mathlib.Analysis.Calculus.FDeriv.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import InfoGeometry.Analysis.PositiveOrthantLogPotentialCalculus
import InfoGeometry.Analysis.LogVolumePathIntegral
import InfoGeometry.Continuous.PositiveOrthant

/-!
# The finite positive-orthant exact-form bridge

This owner keeps the continuous statement on the concrete open positive
orthant chart.  It does not identify the projective quotient with a smooth
manifold.  The coordinate logarithm is the scalar 0-form and its Fréchet
derivative is the corresponding exact chart 1-form.
-/

set_option linter.unusedSectionVars false

noncomputable section

namespace InfoGeometry.Continuous.DeRhamBridge

open InfoGeometry.Projective
open InfoGeometry.Analysis.PositiveOrthantLogPotentialCalculus
open InfoGeometry.Analysis.LogVolumeExactDifferential
open InfoGeometry.Analysis.LogVolumePathIntegral
open MeasureTheory
open scoped Interval

variable {α : Type*} [Fintype α]

abbrev Chart (α : Type*) := EuclideanSpace ℝ α

def zeroForm (i : α) : Chart α → ℝ := coordinateLogPotential i

noncomputable def exactOneForm (i : α) (x : Chart α) : Chart α →L[ℝ] ℝ :=
  (1 / x i) • coordinateCLM i

theorem zeroForm_hasFDerivAt
    (i : α) {x : Chart α} (hx : x i ≠ 0) :
    HasFDerivAt (zeroForm i) (exactOneForm i x) x := by
  exact hasFDerivAt_coordinateLogPotential i hx

theorem zeroForm_contDiffOn_positiveOrthant
    (i : α) :
    ContDiffOn ℝ (⊤ : WithTop ℕ∞) (zeroForm i)
      (interior (positiveOrthantCone (α := α) : Set (Chart α))) := by
  exact coordinateLogPotential_contDiffOn i

theorem exactOneForm_is_derivative
    (i : α) {x : Chart α} (hx : x i ≠ 0) :
    fderiv ℝ (zeroForm i) x = exactOneForm i x := by
  exact (zeroForm_hasFDerivAt i hx).fderiv

theorem exactOneForm_path_integral
    (i : α) {γ : ℝ → Chart α} {a b : ℝ}
    (hγ : ∀ t ∈ Set.uIcc a b, DifferentiableAt ℝ γ t)
    (hpos : ∀ t ∈ Set.uIcc a b, 0 < γ t i)
    (hint : IntervalIntegrable
      (logVolumeDifferential (fun t => γ t i)) volume a b) :
    ∫ t in a..b, logVolumeDifferential (fun t => γ t i) t =
      zeroForm i (γ b) - zeroForm i (γ a) := by
  exact integral_coordinateLogRate_eq_potential_sub i hγ hpos hint

/-! The exact one-form has zero integral on a closed coordinate path. -/
theorem exactOneForm_closed_loop
    (i : α) {γ : ℝ → Chart α} {a b : ℝ}
    (hγ : ∀ t ∈ Set.uIcc a b, DifferentiableAt ℝ γ t)
    (hpos : ∀ t ∈ Set.uIcc a b, 0 < γ t i)
    (hint : IntervalIntegrable
      (logVolumeDifferential (fun t => γ t i)) volume a b)
    (hloop : γ b = γ a) :
    ∫ t in a..b, logVolumeDifferential (fun t => γ t i) t = 0 := by
  rw [exactOneForm_path_integral i hγ hpos hint]
  rw [hloop]
  ring

/-! Reversing the orientation negates the integral of the exact one-form. -/
theorem exactOneForm_path_integral_antisymm
    (i : α) {γ : ℝ → Chart α} {a b : ℝ}
    :
    (∫ t in b..a, logVolumeDifferential (fun t => γ t i) t) =
      -∫ t in a..b, logVolumeDifferential (fun t => γ t i) t := by
  rw [intervalIntegral.integral_symm]

end InfoGeometry.Continuous.DeRhamBridge

end noncomputable section
