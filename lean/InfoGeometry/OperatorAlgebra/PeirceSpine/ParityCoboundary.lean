import InfoGeometry.OperatorAlgebra.PeirceSpine.ParityProducts
import Mathlib.Algebra.Ring.Aut

/-!
# Additive coboundaries and the parity difference

For the action of ring automorphisms on the additive group, `g ↦ X-g(X)`
satisfies the additive cocycle identity. It is explicitly a coboundary.
This does not identify the quadratic defect with a cohomology class or
assert Hilbert 90. No commutativity or characteristic restriction is used.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

/-- The additive coboundary of X, with the sign convention X minus g(X). -/
def automorphismCoboundary (X : B) (g : B ≃+* B) : B := X - g X

theorem automorphismCoboundary_one (X : B) :
    automorphismCoboundary X (1 : B ≃+* B) = 0 := by
  simp [automorphismCoboundary]

/-- The group cocycle law for the additive action on the ambient ring. -/
theorem automorphismCoboundary_mul (X : B) (g h : B ≃+* B) :
    automorphismCoboundary X (g * h) =
      automorphismCoboundary X g + g (automorphismCoboundary X h) := by
  change X - g (h X) = (X - g X) + g (X - h X)
  rw [map_sub]
  abel

/-- For fixed g the difference is additive, but generally not multiplicative. -/
def automorphismDifference (g : B ≃+* B) : B →+ B where
  toFun X := X - g X
  map_zero' := by simp
  map_add' X Y := by simp only [map_add]; abel

theorem automorphismDifference_mul (g : B ≃+* B) (X Y : B) :
    automorphismDifference g (X * Y) =
      automorphismDifference g X * Y + g X * automorphismDifference g Y := by
  change X * Y - g (X * Y) = (X - g X) * Y + g X * (Y - g Y)
  rw [map_mul]
  noncomm_ring

theorem automorphismDifference_eq_zero_iff (g : B ≃+* B) (X : B) :
    automorphismDifference g X = 0 ↔ g X = X := by
  change X - g X = 0 ↔ g X = X
  rw [sub_eq_zero, eq_comm]

variable {P : B} (hP : P * P = P)

/-- The additive parity difference takes values in the kernel of the trace. -/
theorem parityDifference_trace_zero (X : B) :
    automorphismDifference (parityConjRingEquiv hP) X +
      parityConjRingEquiv hP (automorphismDifference (parityConjRingEquiv hP) X) = 0 := by
  change (X - parityConjRingEquiv hP X) +
    parityConjRingEquiv hP (X - parityConjRingEquiv hP X) = 0
  rw [map_sub]
  change (X - parityConj P X) + (parityConj P X - parityConj P (parityConj P X)) = 0
  rw [(parityConj_involutive_ring_action hP X 1).1]
  abel

theorem parityDifference_eq_two_odd (X : B) :
    automorphismDifference (parityConjRingEquiv hP) X = (2 : ℤ) • oddGrade P X :=
  parity_orbit_difference_eq_two_odd X

end InfoGeometry.OperatorAlgebra.PeirceSpine
