import InfoGeometry.Clifford.Cl55DiscreteRoPERepresentation
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-! A parameterized winding-to-rotor composition.

The source type is intentionally an arbitrary additive monoid: a future
topological owner may instantiate it with a genuine winding group, but this
file does not manufacture a fundamental group or monodromy map. -/

noncomputable section

namespace InfoGeometry.Clifford.Cl55WindingRotorBridge

open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Clifford.Cl55DiscreteRoPERepresentation

variable {G : Type*} [AddGroup G]

def windingRotor (w : G →+ ℤ) (i : Fin 5) (theta : ℝ) (g : G) : Cl55 :=
  ropeRotor55Int i theta (w g)

theorem windingRotor_zero (w : G →+ ℤ) (i : Fin 5) (theta : ℝ) :
    windingRotor w i theta 0 = 1 := by
  unfold windingRotor
  rw [map_zero, ropeRotor55Int_zero]

theorem windingRotor_add (w : G →+ ℤ) (i : Fin 5) (theta : ℝ) (g h : G) :
    windingRotor w i theta (g + h) =
      windingRotor w i theta g * windingRotor w i theta h := by
  unfold windingRotor
  rw [map_add, ropeRotor55Int_add]

theorem windingRotor_inverse (w : G →+ ℤ) (i : Fin 5) (theta : ℝ) (g : G)
    : windingRotor w i theta g * windingRotor w i theta (-g) = 1 := by
  unfold windingRotor
  rw [map_neg]
  exact ropeRotor55Int_inverse i theta (w g)

end InfoGeometry.Clifford.Cl55WindingRotorBridge
