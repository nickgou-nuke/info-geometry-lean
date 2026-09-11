import InfoGeometry.Canonical.KleinPresentedGroup
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Orientation character of the algebraic Klein presentation

The presentation has a canonical parity readout: the glide generator `a` is
odd and the transverse generator `b` is even.  The target is the native
multiplicative wrapper of `ZMod 2`; no topological orientation bundle or
operator-algebraic crossed product is asserted.
-/

namespace InfoGeometry.Canonical.KleinOrientationCharacter

open InfoGeometry.Canonical.KleinPresentedGroup

abbrev OrientationGroup := Multiplicative (ZMod 2)

def orientationA : OrientationGroup := Multiplicative.ofAdd 1

def orientationB : OrientationGroup := Multiplicative.ofAdd 0

theorem orientation_relation :
    orientationA * orientationB * orientationA⁻¹ = orientationB⁻¹ := by
  simp [orientationA, orientationB]

/-- The orientation character of the presented Klein group. -/
def orientationCharacter : KleinGroup →* OrientationGroup :=
  kleinRep orientationA orientationB orientation_relation

@[simp] theorem orientationCharacter_genA :
    orientationCharacter (toKlein genA) = orientationA := by
  exact (kleinRep_relator_relation orientationA orientationB
    orientation_relation).1

@[simp] theorem orientationCharacter_genB :
    orientationCharacter (toKlein genB) = orientationB := by
  exact (kleinRep_relator_relation orientationA orientationB
    orientation_relation).2

theorem orientationCharacter_genA_ne_one :
    orientationCharacter (toKlein genA) ≠ 1 := by
  rw [orientationCharacter_genA]
  native_decide

@[simp] theorem orientationCharacter_square_genA :
    orientationCharacter (toKlein genA * toKlein genA) = 1 := by
  rw [map_mul, orientationCharacter_genA]
  native_decide

end InfoGeometry.Canonical.KleinOrientationCharacter
