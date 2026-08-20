import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

import InfoGeometry.Analysis.PositiveOrthantLogPotentialCalculus

/-!
# Calculus of the positive-orthant surprisal potential

This owner is the negative-log readout of the existing coordinate logarithm
owner.  It stays on the concrete Euclidean positive cone; it does not identify
the quotient-valued `PositiveRay` with a smooth manifold.
-/

noncomputable section

namespace InfoGeometry.Analysis.PositiveOrthantSurprisalCalculus

open InfoGeometry.Analysis.PositiveOrthantLogPotentialCalculus
open InfoGeometry.Analysis.LogVolumePathIntegral
open InfoGeometry.Analysis.LogVolumeExactDifferential
open MeasureTheory
open scoped Interval

variable {α : Type*} [Fintype α]

abbrev Chart (α : Type*) := EuclideanSpace ℝ α

/-- The coordinate surprisal is the negative logarithmic potential. -/
def coordinateSurprisalPotential (i : α) : Chart α → ℝ :=
  fun x => -coordinateLogPotential i x

theorem hasFDerivAt_coordinateSurprisalPotential
    (i : α) {x : Chart α} (hx : x i ≠ 0) :
    HasFDerivAt (coordinateSurprisalPotential i)
      (-((1 / x i) • coordinateCLM i)) x := by
  simpa [coordinateSurprisalPotential] using
    (hasFDerivAt_coordinateLogPotential i hx).neg

theorem coordinateSurprisalPotential_contDiffOn
    (i : α) :
    ContDiffOn ℝ (⊤ : WithTop ℕ∞) (coordinateSurprisalPotential i)
      (interior (InfoGeometry.Projective.positiveOrthantCone (α := α) : Set (Chart α))) := by
  intro x hx
  have hxi : 0 < x i :=
    (InfoGeometry.Projective.mem_interior_positiveOrthantCone_iff (α := α) x).mp hx i
  have hlog : ContDiffAt ℝ (⊤ : WithTop ℕ∞) Real.log (x i) :=
    (Real.contDiffAt_log).2 (ne_of_gt hxi)
  exact ((hlog.comp x ((coordinateCLM i).contDiff.contDiffAt)).neg).contDiffWithinAt

theorem integral_coordinateSurprisalRate_eq_potential_sub
    (i : α) {γ : ℝ → Chart α} {a b : ℝ}
    (hγ : ∀ t ∈ Set.uIcc a b, DifferentiableAt ℝ γ t)
    (hpos : ∀ t ∈ Set.uIcc a b, 0 < γ t i)
    (hint : IntervalIntegrable
      (logVolumeDifferential (fun t => γ t i)) volume a b) :
    ∫ t in a..b, -logVolumeDifferential (fun t => γ t i) t =
      coordinateSurprisalPotential i (γ b) -
        coordinateSurprisalPotential i (γ a) := by
  rw [intervalIntegral.integral_neg]
  rw [integral_coordinateLogRate_eq_potential_sub i hγ hpos hint]
  simp only [coordinateSurprisalPotential]
  ring

theorem coordinateSurprisalPotential_difference
    (i : α) (x y : Chart α) :
    coordinateSurprisalPotential i y - coordinateSurprisalPotential i x =
      -coordinateLogPotential i y + coordinateLogPotential i x := by
  simp [coordinateSurprisalPotential]

theorem coordinateSurprisalPotential_closed_loop
    (i : α) (x y : Chart α) (hxy : y i = x i) :
    coordinateSurprisalPotential i y = coordinateSurprisalPotential i x := by
  simp [coordinateSurprisalPotential, coordinateLogPotential, hxy]

end InfoGeometry.Analysis.PositiveOrthantSurprisalCalculus

end noncomputable section
