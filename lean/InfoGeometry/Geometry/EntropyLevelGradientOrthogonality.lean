import Mathlib.Analysis.InnerProductSpace.Calculus
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Gradient orthogonality to entropy level tangents

This is the Hilbert-space theorem underneath the Souriau foliation language.
The differential is an actual continuous linear functional and its gradient is
its Riesz representative.  Hence vectors annihilated by the differential are
orthogonal to the gradient, and motion in the positive gradient direction has
nonnegative first-order entropy production.
-/

noncomputable section

namespace InfoGeometry.Geometry.EntropyLevelGradientOrthogonality

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Riesz gradient of a concrete continuous differential. -/
def rieszGradient (dS : E →L[ℝ] ℝ) : E :=
  (InnerProductSpace.toDual ℝ E).symm dS

/-- The Riesz gradient represents the supplied differential exactly. -/
theorem inner_rieszGradient (dS : E →L[ℝ] ℝ) (Y : E) :
    inner ℝ (rieszGradient dS) Y = dS Y := by
  exact InnerProductSpace.toDual_symm_apply
    (𝕜 := ℝ) (E := E) (x := Y) (y := dS)

/-- Every tangent direction to the linearized entropy level set is orthogonal
to the entropy gradient. -/
theorem rieszGradient_orthogonal_of_mem_ker
    (dS : E →L[ℝ] ℝ) (Y : E) (hY : dS Y = 0) :
    inner ℝ (rieszGradient dS) Y = 0 := by
  rw [inner_rieszGradient, hY]

/-- The differential evaluated on its positive-gradient direction is the
squared norm of that gradient. -/
theorem differential_rieszGradient_eq_norm_sq (dS : E →L[ℝ] ℝ) :
    dS (rieszGradient dS) = ‖rieszGradient dS‖ ^ 2 := by
  rw [← inner_rieszGradient, real_inner_self_eq_norm_sq]

/-- Positive-gradient motion has nonnegative first-order entropy production. -/
theorem differential_rieszGradient_nonneg (dS : E →L[ℝ] ℝ) :
    0 ≤ dS (rieszGradient dS) := by
  rw [differential_rieszGradient_eq_norm_sq]
  positivity

end InfoGeometry.Geometry.EntropyLevelGradientOrthogonality
