import Mathlib.Analysis.Calculus.ContDiff.Operations

import InfoGeometry.Analysis.PositiveOrthantSurprisalCalculus

/-!
# Finite-coordinate surprisal potential

The coordinate negative logarithms are owned by
`PositiveOrthantSurprisalCalculus`.  This file adds their finite sum as a
single smooth scalar potential on the positive cone.
-/

noncomputable section

namespace InfoGeometry.Continuous.SurprisalPotential

open InfoGeometry.Analysis.PositiveOrthantSurprisalCalculus

variable {α : Type*} [Fintype α]

abbrev Chart (α : Type*) := EuclideanSpace ℝ α

def totalSurprisalPotential : Chart α → ℝ :=
  fun x => ∑ i : α, coordinateSurprisalPotential i x

theorem totalSurprisalPotential_contDiffOn :
    ContDiffOn ℝ (⊤ : WithTop ℕ∞) (totalSurprisalPotential (α := α))
      (interior (InfoGeometry.Projective.positiveOrthantCone (α := α) :
        Set (Chart α))) := by
  unfold totalSurprisalPotential
  exact ContDiffOn.sum (fun i _ =>
    coordinateSurprisalPotential_contDiffOn i)

theorem totalSurprisalPotential_apply (x : Chart α) :
    totalSurprisalPotential x =
      ∑ i : α, coordinateSurprisalPotential i x := rfl

end InfoGeometry.Continuous.SurprisalPotential

end noncomputable section
