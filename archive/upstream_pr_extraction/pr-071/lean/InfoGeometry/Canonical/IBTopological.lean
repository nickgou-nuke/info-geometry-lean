import InfoGeometry.Canonical.IBMeasure
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.Moments.Tilted

open MeasureTheory
open ProbabilityTheory

namespace InfoGeometry.Canonical.IBTopological

open IBMeasure

variable {X T : Type*} [MeasurableSpace X] [MeasurableSpace T] [Nonempty T]
variable (qT : Measure T) [IsProbabilityMeasure qT]
variable (D : X → T → ℝ) (x : X)

/-- Log-partition / free-energy generator as the cumulant-generating function of the distortion. -/
noncomputable def F (β : ℝ) : ℝ :=
  cgf (distortionRV D x) qT β

omit [MeasurableSpace X] [Nonempty T] [IsProbabilityMeasure qT] in
/-- Canonical Gibbs measure from mathlib's normalized exponential tilt. -/
noncomputable def Gibbs (β : ℝ) : Measure T :=
  IBGibbsMeasure qT β D x

omit [MeasurableSpace X] [Nonempty T] [IsProbabilityMeasure qT] in
theorem F_deriv_eq_neg_gibbsExpectation
    {β : ℝ}
    (hβ : β ∈ interior (integrableExpSet (distortionRV D x) qT)) :
    deriv (F qT D x) β = - ∫ t, D x t ∂(Gibbs qT D x β) := by
  have h :=
    ProbabilityTheory.integral_tilted_mul_self
      (μ := qT) (X := distortionRV D x) (t := β) hβ
  calc
    deriv (F qT D x) β = ∫ t, distortionRV D x t ∂(Gibbs qT D x β) := by
      simpa [F, Gibbs, IBGibbsMeasure, mul_comm, mul_left_comm, mul_assoc] using h.symm
    _ = - ∫ t, D x t ∂(Gibbs qT D x β) := by
      simpa [distortionRV] using
        (integral_neg (f := fun t => D x t) (μ := Gibbs qT D x β))

omit [MeasurableSpace X] [Nonempty T] [IsProbabilityMeasure qT] in
theorem F_secondDeriv_eq_variance
    {β : ℝ}
    (hβ : β ∈ interior (integrableExpSet (distortionRV D x) qT)) :
    iteratedDeriv 2 (F qT D x) β
      = ProbabilityTheory.variance (distortionRV D x) (Gibbs qT D x β) := by
  simpa [F, Gibbs, IBGibbsMeasure, mul_comm, mul_left_comm, mul_assoc] using
    (ProbabilityTheory.variance_tilted_mul
      (μ := qT) (X := distortionRV D x) (t := β) hβ).symm

end InfoGeometry.Canonical.IBTopological
