import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
namespace InfoGeometry.SignedNetwork.RegularBimoduleSeparation
variable {A : Type*} [Ring A]
def leftAction (a : A) : A →+ A := { toFun := fun x => a*x, map_zero' := mul_zero a, map_add' := fun x y => mul_add a x y }
def rightAction (b : A) : A →+ A := { toFun := fun x => x*b, map_zero' := zero_mul b, map_add' := fun x y => add_mul x y b }
theorem left_right_commute (a b : A) : (leftAction a).comp (rightAction b) = (rightAction b).comp (leftAction a) := by
  ext x
  simp [leftAction, rightAction, mul_assoc]
theorem commutant_characterization (T : A →+ A) :
    (∀ a x, T (a*x) = a*T x) ↔ ∀ x, T x = x * T 1 := by
  constructor
  · intro h x
    simpa using h x 1
  · intro h a x
    rw [h (a*x), h x]
    simp [mul_assoc]
end InfoGeometry.SignedNetwork.RegularBimoduleSeparation
