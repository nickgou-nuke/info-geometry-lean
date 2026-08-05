import InfoGeometry.Algebra.Grothendieck
import InfoGeometry.Physics.Algebra.TripotentPeirceProjectors

/-!
# Grothendieck classes of Peirce projectors

This file records only the additive Grothendieck-group shadow of the Peirce
polynomial calculus.  It does not identify these classes with `K₀` classes:
the local `Grothendieck` owner is an additive group completion, not yet a
projective-module or idempotent-equivalence construction.
-/

namespace InfoGeometry.Canonical.PeirceProjectorGrothendieckClass

noncomputable section

open InfoGeometry.Physics.Algebra

variable {R : Type*} [Ring R] [Algebra ℝ R]

/-- The additive Grothendieck class of an element of the coefficient ring. -/
def classOf (x : R) : Grothendieck R :=
  grothendieckMap R x

omit [Algebra ℝ R] in
@[simp] theorem classOf_apply (x : R) :
    classOf x = grothendieckMap R x := rfl

omit [Algebra ℝ R] in
@[simp] theorem classOf_add (x y : R) :
    classOf (x + y) = classOf x + classOf y :=
  (grothendieckMap R).map_add x y

/--
The three Peirce polynomial classes reconstruct the class of the unit.
This uses only the additive projector reconstruction identity, so no
tripotency hypothesis is required here.
-/
theorem peirce_projector_class_sum (T : R) :
    classOf (projPos T) + classOf (projZero T) + classOf (projNeg T) =
      classOf (1 : R) := by
  simpa only [classOf, map_add] using
    congrArg
      (fun x : R => grothendieckMap R x)
      (proj_sum_eq_id (T := T))

/-! The same statement with the tripotent hypothesis made explicit for
downstream APIs that carry it as part of their data. -/

theorem peirce_projector_class_sum_of_tripotent
    (T : R) (_hT : T * T * T = T) :
    classOf (projPos T) + classOf (projZero T) + classOf (projNeg T) =
      classOf (1 : R) := by
  exact peirce_projector_class_sum T

end
end InfoGeometry.Canonical.PeirceProjectorGrothendieckClass
