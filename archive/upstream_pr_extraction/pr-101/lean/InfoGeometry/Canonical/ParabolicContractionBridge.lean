import InfoGeometry.Canonical.GeneralizedOperatorChiral

/-!
# InfoGeometry.Canonical.ParabolicContractionBridge

Correct finite `Ω² = 0` contraction bridge on the generalized-operator lane.

This module avoids extra algebraic typeclass assumptions and formalizes:

* collapsed Poisson lane (`0`),
* parabolic metric lane (`mul` at `sq_val = 0`),
* Leibniz reduction to metric,
* nontrivial metric kernel on pure nilpotent directions,
* pure nilpotent exponential composition.
-/

namespace InfoGeometry.Canonical.ParabolicContractionBridge

open GeneralizedOperatorChiral
open GeneralizedOperator

abbrev ParOp := GeneralizedOperator 0

def poissonParabolic : ParOp → ParOp → ParOp := fun _ _ => zero
def metricParabolic : ParOp → ParOp → ParOp := fun A B => mul A B
def leibnizParabolic : ParOp → ParOp → ParOp := fun A B => add (poissonParabolic A B) (metricParabolic A B)

theorem metricParabolic_symm (A B : ParOp) :
  metricParabolic A B = metricParabolic B A := by
  apply GeneralizedOperator.ext <;>
  dsimp [metricParabolic, mul] <;> ring

theorem leibnizParabolic_eq_metric (A B : ParOp) :
  leibnizParabolic A B = metricParabolic A B := by
  apply GeneralizedOperator.ext <;>
  dsimp [leibnizParabolic, poissonParabolic, metricParabolic, add, zero] <;> ring

theorem metricParabolic_kernel_nilpotent (χ : ℝ) :
  metricParabolic ({ scalar := (0 : ℝ), directional := χ } : ParOp)
      ({ scalar := (0 : ℝ), directional := χ } : ParOp) = zero := by
  simpa [metricParabolic] using
    (GeneralizedOperator.parabolic_pure_square_zero χ)


theorem parabolicExp_pure_composition (χ₁ χ₂ : ℝ) :
  GeneralizedOperator.parabolicExp
    ({ scalar := (0 : ℝ), directional := χ₁ + χ₂ } : ParOp)
    =
    metricParabolic
    (GeneralizedOperator.parabolicExp
      ({ scalar := (0 : ℝ), directional := χ₁ } : ParOp))
    (GeneralizedOperator.parabolicExp
      ({ scalar := (0 : ℝ), directional := χ₂ } : ParOp)) := by
  simpa [metricParabolic] using
    (GeneralizedOperator.parabolicExp_pure_nilpotent_add χ₁ χ₂)

end InfoGeometry.Canonical.ParabolicContractionBridge
