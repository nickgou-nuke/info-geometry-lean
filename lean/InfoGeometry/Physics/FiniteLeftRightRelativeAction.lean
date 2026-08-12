import InfoGeometry.Physics.RegularBimoduleCommutant
import InfoGeometry.Physics.AlgebraicTomitaTakesakiBridge

/-!
# Finite left/right relative action

The regular bimodule already carries commuting left and right actions.  This
file exposes their difference as a finite algebraic relative generator.  It
is deliberately not named a modular logarithm: identifying it with
`-log Δ` requires a faithful state and a Hilbert-space standard form.
-/

namespace InfoGeometry.Physics.FiniteLeftRightRelativeAction

open InfoGeometry.Physics.RegularBimoduleCommutant

variable {R A : Type*} [CommSemiring R] [Ring A] [Algebra R A]

/-- The relative left/right generator on the regular bimodule. -/
def relativeAction (a : A) : A →ₗ[R] A :=
  leftAction (R := R) a - rightAction (R := R) a

@[simp] theorem relativeAction_apply (a x : A) :
    relativeAction (R := R) a x = a * x - x * a := by
  simp [relativeAction, leftAction, rightAction]

theorem leftRight_commute (a b : A) :
    (leftAction (R := R) a).comp (rightAction (R := R) b) =
      (rightAction (R := R) b).comp (leftAction (R := R) a) := by
  ext x
  simp [leftAction, rightAction, LinearMap.comp_apply, mul_assoc]

theorem relativeAction_eq_zero_of_central (a : A)
    (ha : ∀ x : A, a * x = x * a) :
    relativeAction (R := R) a = 0 := by
  ext x
  simp [relativeAction_apply, ha]

theorem relativeAction_add (a b : A) :
    relativeAction (R := R) (a + b) =
      relativeAction (R := R) a + relativeAction (R := R) b := by
  ext x
  simp [relativeAction_apply, add_mul, mul_add, sub_eq_add_neg,
    add_assoc, add_left_comm, add_comm]

theorem relativeAction_neg (a : A) :
    relativeAction (R := R) (-a) = -relativeAction (R := R) a := by
  ext x
  simp [relativeAction_apply, neg_mul, mul_neg, sub_eq_add_neg,
    add_comm]

theorem antiAutomorphism_apply_relativeAction
    (J : AntiAutomorphism A) (a x : A) :
    J.toFun (relativeAction (R := R) a x) =
      -relativeAction (R := R) (J.toFun a) (J.toFun x) := by
  have hz : J.toFun 0 = 0 := by
    have h := J.map_add 0 0
    have h' : J.toFun 0 = J.toFun 0 + J.toFun 0 := by
      simpa using h
    have h'' : 0 = J.toFun 0 := by
      calc
        0 = J.toFun 0 - J.toFun 0 := by simp
        _ = (J.toFun 0 + J.toFun 0) - J.toFun 0 := by rw [← h']
        _ = J.toFun 0 := by simp [sub_eq_add_neg, add_assoc]
    exact h''.symm
  have hneg (y : A) : J.toFun (-y) = -J.toFun y := by
    have hsum : J.toFun (-y) + J.toFun y = J.toFun 0 := by
      simpa using (J.map_add (-y) y).symm
    calc
      J.toFun (-y) = J.toFun (-y) + J.toFun y - J.toFun y := by simp
      _ = J.toFun 0 - J.toFun y := by rw [hsum]
      _ = -J.toFun y := by rw [hz]; simp
  rw [relativeAction_apply, sub_eq_add_neg, J.map_add, hneg, J.map_mul,
    J.map_mul]
  simp [relativeAction_apply, sub_eq_add_neg]

end InfoGeometry.Physics.FiniteLeftRightRelativeAction
