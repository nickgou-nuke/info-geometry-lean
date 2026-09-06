import Mathlib.Tactic
import Mathlib.Geometry.Euclidean.Inversion.Basic

/-!
# InfoGeometry.Canonical.ConformalInversionCore

Direct canonical inversion core.

This file does not wrap a bridge theorem. It records the radial inversion map
`x ↦ ‖x‖⁻² • x` on a punctured normed space and the elementary fact that the
unit sphere is fixed.
-/

noncomputable section

namespace InfoGeometry.Canonical.ConformalInversionCore

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

open EuclideanGeometry

/-- Radial conformal inversion centered at the origin and unit radius. -/
def conformalInversion (x : E) : E := inversion (0 : E) 1 x

@[simp] theorem conformalInversion_apply (x : E) :
    conformalInversion (E := E) x = inversion (0 : E) 1 x := by
  rfl

/-- `x ↦ x` is recovered by double inversion. -/
theorem conformalInversion_involutive (x : E) :
    conformalInversion (E := E) (conformalInversion (E := E) x) = x := by
  simpa [conformalInversion] using
    (inversion_inversion (c := (0 : E)) (R := (1 : ℝ)) (one_ne_zero : (1 : ℝ) ≠ 0) x)

section UnitSphere

/-
Unit-norm vectors are fixed points of conformal inversion.
-/
theorem conformalInversion_fixed_of_norm_one (x : E) (hx : ‖x‖ = 1) :
    conformalInversion (E := E) x = x := by
  simpa [conformalInversion, Metric.mem_sphere, dist_eq_norm] using
    (inversion_of_mem_sphere
      (c := (0 : E)) (R := (1 : ℝ)) (by simpa [Metric.mem_sphere, dist_eq_norm] using hx))

end UnitSphere

end InfoGeometry.Canonical.ConformalInversionCore
