/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.JordanAssociatorRing

/-! Exact scopes for the proposed triple formula, on the original associative
ring. The pointwise obstruction `[z,x] * y` is owned by JordanAssociatorRing.
Requiring the formula for every middle input, or for an invertible middle
input, detects commutation of the endpoints. No ambient commutativity is used.
-/

namespace InfoGeometry.Core.JordanAssociator
variable {R : Type*} [Ring R]

theorem proposed_triple_forall_middle_iff (x z : R) :
    (∀ y : R, (x * y) * z + z * (x * y) - (x * (z * y) - (z * y) * x) =
      x * y * z + z * y * x) ↔ Commute z x := by
  simp only [proposed_triple_formula_iff_obstruction_vanishes]
  constructor
  · intro h
    exact sub_eq_zero.mp (by simpa using h 1)
  · intro h y
    rw [h.eq, sub_self, zero_mul]

theorem proposed_triple_unit_middle_iff (x z : R) (y : Rˣ) :
    (x * (y : R)) * z + z * (x * (y : R)) -
        (x * (z * (y : R)) - (z * (y : R)) * x) =
      x * (y : R) * z + z * (y : R) * x ↔ Commute z x := by
  rw [proposed_triple_formula_iff_obstruction_vanishes]
  constructor
  · intro h
    have hc := congrArg (fun t : R => t * (↑y⁻¹ : R)) h
    have hy : (y : R) * (↑y⁻¹ : R) = 1 := y.val_inv
    rw [mul_assoc, hy, mul_one, zero_mul] at hc
    exact sub_eq_zero.mp hc
  · intro h
    rw [h.eq, sub_self, zero_mul]

/-- Any noncommuting endpoint pair gives a concrete failure witness for the
proposed triple formula: the unit is a middle input for which the formula
cannot hold. -/
theorem proposed_triple_formula_fails_at_one_of_noncommuting
    (x z : R) (h : z * x ≠ x * z) :
    ((x * (1 : R)) * z + z * (x * (1 : R)) -
        (x * (z * (1 : R)) - (z * (1 : R)) * x)) ≠
      x * (1 : R) * z + z * (1 : R) * x := by
  intro hFormula
  have hObs :=
    (proposed_triple_formula_iff_obstruction_vanishes x (1 : R) z).mp hFormula
  have hComm : z * x - x * z = 0 := by simpa using hObs
  exact h (sub_eq_zero.mp hComm)

end InfoGeometry.Core.JordanAssociator
