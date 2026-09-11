import InfoGeometry.Physics.RegularBimoduleCommutant
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.AlgebraicTomitaTakesakiBridge
import InfoGeometry.Krein.TwoSheetKreinIdealBridge

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

open InfoGeometry.Krein

theorem antiAutomorphism_leftPrincipal_iff_rightPrincipal
    (J : AntiAutomorphism A) (f x : A) :
    x ∈ leftPrincipal f ↔ J.toFun x ∈ rightPrincipal (J.toFun f) := by
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨J.toFun a, ?_⟩
    exact (J.map_mul a f).symm
  · rintro ⟨a, ha⟩
    have hxa : J.toFun (J.toFun x) = J.toFun (J.toFun f * a) :=
      congrArg J.toFun ha.symm
    rw [J.inv x, J.map_mul, J.inv f] at hxa
    exact ⟨J.toFun a, hxa.symm⟩

/-- The relative left/right generator on the regular bimodule. -/
def relativeAction (a : A) : A →ₗ[R] A :=
  leftAction (R := R) a - rightAction (R := R) a

/-- The finite left-right quadratic action associated with an algebraic
Tomita-style anti-automorphism.  The second factor acts from the commuting
right side of the regular bimodule.  This is an algebraic readout only: no
positivity or analytic standard-form assertion is made here. -/
def commutantQuadraticAction
    (J : InfoGeometry.Physics.AntiAutomorphism A) (a : A) : A →ₗ[R] A :=
  (leftAction (R := R) a).comp (rightAction (R := R) (J.toFun a))

@[simp] theorem commutantQuadraticAction_apply
    (J : InfoGeometry.Physics.AntiAutomorphism A) (a x : A) :
    commutantQuadraticAction (R := R) J a x = a * x * J.toFun a := by
  simp [commutantQuadraticAction, leftAction, rightAction,
    LinearMap.comp_apply, mul_assoc]

@[simp] theorem relativeAction_apply (a x : A) :
    relativeAction (R := R) a x = a * x - x * a := by
  simp [relativeAction, leftAction, rightAction]

theorem map_relativeAction_apply
    {B : Type*} [Ring B] (f : A →+* B) (a x : A) :
    f (relativeAction (R := R) a x) =
      f a * f x - f x * f a := by
  rw [relativeAction_apply, map_sub, map_mul, map_mul]

theorem leftRight_commute (a b : A) :
    (leftAction (R := R) a).comp (rightAction (R := R) b) =
      (rightAction (R := R) b).comp (leftAction (R := R) a) := by
  ext x
  simp [leftAction, rightAction, LinearMap.comp_apply, mul_assoc]

theorem commutantQuadraticAction_commuting_factors
    (J : InfoGeometry.Physics.AntiAutomorphism A) (a : A) :
    (leftAction (R := R) a).comp (rightAction (R := R) (J.toFun a)) =
      (rightAction (R := R) (J.toFun a)).comp (leftAction (R := R) a) := by
  exact leftRight_commute a (J.toFun a)

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

/- The commutator action satisfies the Leibniz rule in its algebra argument. -/
theorem relativeAction_mul (a b x : A) :
    relativeAction (R := R) (a * b) x =
      a * relativeAction (R := R) b x +
        relativeAction (R := R) a x * b := by
  simp only [relativeAction_apply]
  noncomm_ring

/- Inner commutators form a Lie action on the regular bimodule. -/
theorem relativeAction_commutator (a b x : A) :
    relativeAction (R := R) a (relativeAction (R := R) b x) -
      relativeAction (R := R) b (relativeAction (R := R) a x) =
        relativeAction (R := R) (a * b - b * a) x := by
  simp only [relativeAction_apply]
  noncomm_ring

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
