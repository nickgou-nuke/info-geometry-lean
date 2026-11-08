import InfoGeometry.Clifford.Cl55RoPESplitTorusBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-! Discrete-position laws for the native elliptic `Cl(5,5)` rotor.

This owner records the exact integer-position representation laws in the
Clifford carrier.  It deliberately does not identify this carrier with KZ
monodromy or construct a unit-valued homomorphism. -/

noncomputable section

namespace InfoGeometry.Clifford.Cl55DiscreteRoPERepresentation

open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Clifford.Cl55RoPESplitTorusBridge

def ropeRotor55Int (i : Fin 5) (theta : ℝ) (m : ℤ) : Cl55 :=
  ropeRotor55 i ((m : ℝ) * theta)

theorem ropeRotor55Int_zero (i : Fin 5) (theta : ℝ) :
    ropeRotor55Int i theta 0 = 1 := by
  unfold ropeRotor55Int
  simp [ropeRotor55_zero]

theorem ropeRotor55Int_add (i : Fin 5) (theta : ℝ) (m n : ℤ) :
    ropeRotor55Int i theta (m + n) =
      ropeRotor55Int i theta m * ropeRotor55Int i theta n := by
  unfold ropeRotor55Int
  rw [ropeRotor55_add]
  congr 1
  push_cast
  ring

theorem ropeRotor55Int_inverse (i : Fin 5) (theta : ℝ) (m : ℤ) :
    ropeRotor55Int i theta m * ropeRotor55Int i theta (-m) = 1 := by
  rw [← ropeRotor55Int_add]
  simpa using ropeRotor55Int_zero i theta

theorem ropeRotor55Int_relative (i : Fin 5) (theta : ℝ) (m n : ℤ) :
    ropeRotor55Int i theta (-m) * ropeRotor55Int i theta n =
      ropeRotor55Int i theta (n - m) := by
  rw [← ropeRotor55Int_add]
  congr 1
  push_cast
  ring

end InfoGeometry.Clifford.Cl55DiscreteRoPERepresentation
