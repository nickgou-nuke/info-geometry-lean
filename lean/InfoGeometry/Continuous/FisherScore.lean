import Mathlib.Analysis.Calculus.FDeriv.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic

import InfoGeometry.Analysis.PositiveOrthantSurprisalCalculus

/-!
# Fisher score of the positive-orthant surprisal

This owner records the genuine Fréchet derivative of the coordinate negative
logarithm and of its finite sum.  The relative modular derivative is kept in
its own owner; it is not identified with this scalar surprisal without an
additional theorem about the chosen density model.
-/

noncomputable section

namespace InfoGeometry.Continuous.FisherScore

open InfoGeometry.Analysis.PositiveOrthantSurprisalCalculus
open InfoGeometry.Analysis.PositiveOrthantLogPotentialCalculus

variable {α : Type*} [Fintype α]

abbrev Chart (α : Type*) := EuclideanSpace ℝ α

theorem hasFDerivAt_coordinateSurprisal
    (i : α) {x : Chart α} (hx : x i ≠ 0) :
    HasFDerivAt (coordinateSurprisalPotential i)
      (-((1 / x i) • coordinateCLM i)) x := by
  simpa [coordinateSurprisalPotential, one_div] using
    (hasFDerivAt_coordinateSurprisalPotential i hx)

theorem fisherScore_coordinate_apply
    (i : α) {x : Chart α} (hx : x i ≠ 0) (v : Chart α) :
    (fderiv ℝ (coordinateSurprisalPotential i) x) v =
      -(v i / x i) := by
  have h := hasFDerivAt_coordinateSurprisal i hx
  rw [h.fderiv]
  simp [coordinateCLM_apply, div_eq_mul_inv]
  ring

theorem hasFDerivAt_surprisal_sum
    {x : Chart α} (hx : ∀ i, x i ≠ 0) :
    HasFDerivAt
      (fun y : Chart α => ∑ i : α, coordinateSurprisalPotential i y)
      (∑ i : α, -((1 / x i) • coordinateCLM i)) x := by
  convert HasFDerivAt.sum (fun i _ => hasFDerivAt_coordinateSurprisal i (hx i)) using 1
  · funext y
    simp

theorem fisherScore_sum_apply
    {x : Chart α} (hx : ∀ i, x i ≠ 0) (v : Chart α) :
    (∑ i : α, (fderiv ℝ (coordinateSurprisalPotential i) x) v) =
      ∑ i : α, -(v i / x i) := by
  apply Finset.sum_congr rfl
  intro i hi
  exact fisherScore_coordinate_apply i (hx i) v

end InfoGeometry.Continuous.FisherScore

end noncomputable section
