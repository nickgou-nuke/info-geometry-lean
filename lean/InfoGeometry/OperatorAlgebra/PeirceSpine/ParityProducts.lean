import InfoGeometry.OperatorAlgebra.PeirceSpine.Supercharge

/-!
# Parity trace and ordered products

The existing parity ring equivalence is involutive. Its additive orbit sum
is invariant. Its ordered multiplicative orbit product is invariant precisely
when the element commutes with its parity image; it is not an unconditional
noncommutative Galois norm.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B] {P : B} (hP : P * P = P)
include hP

theorem parityConj_orbit_sum (X : B) :
    parityConj P (X + parityConj P X) = X + parityConj P X := by
  rw [(parityConj_involutive_ring_action hP X (parityConj P X)).2.2.1,
    (parityConj_involutive_ring_action hP X 1).1, add_comm]

theorem parityConj_orbit_product (X : B) :
    parityConj P (X * parityConj P X) = parityConj P X * X := by
  rw [(parityConj_involutive_ring_action hP X (parityConj P X)).2.1,
    (parityConj_involutive_ring_action hP X 1).1]

/-- Exact obstruction to fixedness of the ordered product. -/
theorem parityConj_orbit_product_fixed_iff (X : B) :
    parityConj P (X * parityConj P X) = X * parityConj P X ↔
      Commute X (parityConj P X) := by
  rw [parityConj_orbit_product hP]
  change parityConj P X * X = X * parityConj P X ↔
    X * parityConj P X = parityConj P X * X
  exact eq_comm

omit hP in
/-- A division-free expression for the additive parity orbit sum. -/
theorem parity_orbit_sum_eq_two_even (X : B) :
    X + parityConj P X = (2 : ℤ) • evenGrade P X := by
  simp only [parityConj, invS, evenGrade, two_zsmul]
  noncomm_ring

omit hP in
/-- The complementary signed orbit sum isolates twice the odd part. -/
theorem parity_orbit_difference_eq_two_odd (X : B) :
    X - parityConj P X = (2 : ℤ) • oddGrade P X := by
  simp only [parityConj, invS, oddGrade, two_zsmul]
  noncomm_ring

end InfoGeometry.OperatorAlgebra.PeirceSpine
