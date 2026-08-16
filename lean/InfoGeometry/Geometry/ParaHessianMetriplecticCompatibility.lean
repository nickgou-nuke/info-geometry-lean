import InfoGeometry.Geometry.ParaHessianMixedPotential

/-!
# Para-Hessian compatibility readout

The existing `ParaHessianMixedPotential` owner supplies the neutral metric,
the grading involution, and the skew form.  This file records their exact
compatibility and does not identify the generic metriplectic operators with
these geometric objects.

With the convention

`symplectic U V = metric (grading U) V`,

the right action of the grading contributes a minus sign:

`metric U V = - symplectic U (grading V)`.
-/

namespace InfoGeometry.Geometry.ParaHessianMetriplecticCompatibility

open InfoGeometry.Geometry.ParaHessianMixedPotential

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem metric_eq_neg_symplectic_grading (U V : Doubled E) :
    metric U V = -symplectic U (grading V) := by
  rw [symplectic_apply]
  simp [metric_apply, grading_apply]
  ring

theorem symplectic_eq_metric_grading (U V : Doubled E) :
    symplectic U V = metric (grading U) V := by
  rfl

theorem metric_grading_isometry (U V : Doubled E) :
    metric (grading U) (grading V) = -metric U V :=
  grading_anti_isometry U V

theorem metric_and_symplectic_split (U V : Doubled E) :
    metric U V + symplectic U (grading V) = 0 := by
  rw [metric_eq_neg_symplectic_grading]
  ring

end InfoGeometry.Geometry.ParaHessianMetriplecticCompatibility
