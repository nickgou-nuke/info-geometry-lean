import InfoGeometry.Canonical.ConformalInversionCore

/-!
# InfoGeometry.Canonical.ConformalMobiusJacobian

Direct canonical Möbius/Jacobian package.

This tightens the inversion core into the standard conformal form:

* ambient Möbius inversion `x ↦ x / ‖x‖²`,
* involutivity,
* fixed unit-sphere boundary,
* and the Fréchet derivative readout with its scalar Jacobian factor.

No bridge file is imported here.
-/

noncomputable section

open EuclideanGeometry
open scoped Topology RealInnerProductSpace

namespace InfoGeometry.Canonical.ConformalMobiusJacobian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Ambient Möbius inversion around the origin with unit radius. -/
def mobiusInversion : E → E := EuclideanGeometry.inversion (0 : E) 1

/-- Möbius inversion is involutive. -/
theorem mobiusInversion_involutive : Function.Involutive (mobiusInversion (E := E)) := by
  intro x
  rw [mobiusInversion]
  exact EuclideanGeometry.inversion_inversion (c := (0 : E)) (R := (1 : ℝ))
    (by norm_num) x

/-- The unit sphere is fixed by Möbius inversion. -/
theorem mobiusInversion_fixed_of_norm_one {x : E}
    (hx : ‖x‖ = 1) :
    mobiusInversion (E := E) x = x :=
  EuclideanGeometry.inversion_of_mem_sphere (c := (0 : E)) (R := (1 : ℝ)) (by
    simpa [Metric.mem_sphere, dist_eq_norm] using hx)

/-- Scalar Jacobian factor of the Möbius inversion derivative. -/
def mobiusJacobianFactor (x : E) : ℝ := (1 / dist x (0 : E)) ^ 2

/--
Fréchet derivative of the ambient Möbius inversion.

The derivative is the scalar factor `((1 / dist x 0)^2)` times the orthogonal
reflection across the orthogonal complement of the radial line through `x`.
-/
theorem mobiusInversion_hasFDerivAt {x : E} (hx : x ≠ 0) :
    HasFDerivAt (mobiusInversion (E := E))
      (((1 / dist x (0 : E)) ^ 2) •
        (↑((ℝ ∙ (x - (0 : E)))ᗮ.reflection.toContinuousLinearEquiv) : E →L[ℝ] E)) x := by
  simpa [mobiusInversion] using
    EuclideanGeometry.hasFDerivAt_inversion (c := (0 : E)) (R := (1 : ℝ)) (x := x) hx

/-- Canonical Möbius/Jacobian packet. -/
structure MobiusJacobianPacket (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  inversion : E → E
  involutive : Function.Involutive inversion
  fixed_of_norm_one : ∀ {x : E}, ‖x‖ = 1 → inversion x = x
  jacobianFactor : E → ℝ

section JacobianFactor

variable {E : Type*} [NormedAddCommGroup E]

/-- The scalar Jacobian factor is `1` on the unit sphere. -/
theorem mobiusJacobianFactor_eq_one_of_norm_one {x : E}
    (hx : ‖x‖ = 1) :
    mobiusJacobianFactor (E := E) x = 1 := by
  simp [mobiusJacobianFactor, dist_eq_norm, hx]

end JacobianFactor

/-- The canonical Möbius/Jacobian packet. -/
def standardMobiusJacobianPacket : MobiusJacobianPacket E where
  inversion := mobiusInversion
  involutive := mobiusInversion_involutive
  fixed_of_norm_one := by
    intro x hx
    exact mobiusInversion_fixed_of_norm_one (E := E) hx
  jacobianFactor := mobiusJacobianFactor

end InfoGeometry.Canonical.ConformalMobiusJacobian
