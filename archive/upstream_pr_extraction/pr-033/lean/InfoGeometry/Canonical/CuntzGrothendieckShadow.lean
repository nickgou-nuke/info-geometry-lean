import InfoGeometry.Algebra.Grothendieck
import InfoGeometry.Physics.Algebra.CuntzKGroupStructure

/-!
# Cuntz Grothendieck shadow

This file records the additive Grothendieck-group shadow of the Cuntz
projection completeness theorem.  It does not introduce an abstract operator
`K₀` or a Murray--von Neumann quotient; it only transports the existing
completeness identity through the additive group completion.
-/

namespace InfoGeometry.Canonical.CuntzGrothendieckShadow

open InfoGeometry.Physics.Algebra

variable {A : Type*} [Ring A]

/-- The additive Grothendieck class of an element of the operator ring. -/
def classOf (x : A) : Grothendieck A :=
  grothendieckMap A x

@[simp] theorem classOf_apply (x : A) :
    classOf x = grothendieckMap A x := rfl

@[simp] theorem classOf_add (x y : A) :
    classOf (x + y) = classOf x + classOf y := by
  simp [classOf]

/--
The Cuntz completeness identity survives in the additive Grothendieck shadow.

This is strictly the transported additive statement; it does not claim a full
operator-algebraic `K₀` classification.
-/
theorem cuntz_projector_class_sum
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    (O2 : CuntzTwoAlgebra A) :
    classOf (O2.S1 * O2.S1_star) + classOf (O2.S2 * O2.S2_star) =
      classOf (1 : A) := by
  simpa [classOf] using
    congrArg (grothendieckMap A) (cuntz_projection_completeness (A := A) O2)

end InfoGeometry.Canonical.CuntzGrothendieckShadow
