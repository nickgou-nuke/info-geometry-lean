import InfoGeometry.Algebra.NonCommutativeIsometry
import InfoGeometry.Canonical.CantorBoundaryCuntzShift

/-!
# Deformed Idele Action: finite Cuntz readout

This module formalizes the finite algebraic readout behind the phrase
"deformed idelic action".

The closed theorem surface is deliberately narrow:

* the generic source/range commutator facts are owned by
  `InfoGeometry.Algebra.NonCommutativity`;
* the existing `CuntzO2Carrier` supplies this isometry premise for its left and
  right branches.

No theorem here asserts an adele/idele group, a quantum torus, q-deformation,
Souriau flow, KMS transition, root-of-unity braid representation, Galois action,
C*-completion, zeta theorem, or RH consequence.

#### BUCKET 1: CLOSED FINITE THEOREMS
Cuntz-branch specializations of the generic finite noncommutative isometry
lemmas.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
The projection/idempotence readouts depend only on explicitly named
partial-isometry or Cuntz-isometry premises.

#### BUCKET 3: OPEN CLOSURE DEBT
Classical ideles/adeles, non-commutative torus deformation, q-parameter
dynamics, KMS/BEC physics, braid-group representation theory, and arithmetic
or zeta consequences.
-/

noncomputable section

namespace InfoGeometry.Canonical.DeformedIdeleAction

open InfoGeometry.Topology
open InfoGeometry.Algebra.NonCommutativity

variable {A : Type*} [Ring A] [StarRing A]

/-! ## Cuntz `O₂` branch specializations -/

variable (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) A)

/-- A strict isometry has nonzero range projection. -/
theorem isometry_rangeProjection_ne_zero
    [Nontrivial A]
    (S : A) (hS : star S * S = 1) :
    rangeProjection S ≠ 0 := by
  intro hzero
  have h0 : S * star S = 0 := by
    simpa [rangeProjection] using hzero
  have hstar0 : star S = 0 := by
    have h1 : star S * (S * star S) = 0 := by
      rw [h0, mul_zero]
    have h2 : (star S * S) * star S = 0 := by
      simpa [mul_assoc] using h1
    simpa [hS] using h2
  have hcontr : (0 : A) = 1 := by
    simpa [hstar0] using hS.symm
  exact zero_ne_one hcontr

/-- Left Cuntz branch commutator readout. -/
theorem left_cuntz_branch_commutator :
    InfoGeometry.Topology.CuntzO2Carrier.S_left C * star (InfoGeometry.Topology.CuntzO2Carrier.S_left C) - star (InfoGeometry.Topology.CuntzO2Carrier.S_left C) * InfoGeometry.Topology.CuntzO2Carrier.S_left C =
      InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection C - 1 := by
  unfold InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection
  exact isometry_branch_commutator_eq_range_sub_one (InfoGeometry.Topology.CuntzO2Carrier.S_left C) (InfoGeometry.Topology.CuntzO2Carrier.left_isometry C)

/-- Right Cuntz branch commutator readout. -/
theorem right_cuntz_branch_commutator :
    InfoGeometry.Topology.CuntzO2Carrier.S_right C * star (InfoGeometry.Topology.CuntzO2Carrier.S_right C) - star (InfoGeometry.Topology.CuntzO2Carrier.S_right C) * InfoGeometry.Topology.CuntzO2Carrier.S_right C =
      InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection C - 1 := by
  unfold InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection
  exact isometry_branch_commutator_eq_range_sub_one (InfoGeometry.Topology.CuntzO2Carrier.S_right C) (InfoGeometry.Topology.CuntzO2Carrier.right_isometry C)

/-- Left Cuntz branch range projection is idempotent. -/
theorem left_cuntz_rangeProjection_idempotent :
    InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection C * InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection C = InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection C :=
  InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection_idempotent C

/-- Right Cuntz branch range projection is idempotent. -/
theorem right_cuntz_rangeProjection_idempotent :
    InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection C * InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection C = InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection C :=
  InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection_idempotent C

/-- The two Cuntz range projections form a finite branch partition. -/
theorem cuntz_branch_partition :
    InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection C + InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection C = 1 :=
  InfoGeometry.Topology.CuntzO2Carrier.rangeProjection_sum_one C

/-- Left Cuntz branch commutator is genuinely non-zero when the left projection is strictly less than 1. -/
theorem left_cuntz_branch_commutator_ne_zero
    (h_mismatch : InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection C ≠ 1) :
    InfoGeometry.Topology.CuntzO2Carrier.S_left C * star (InfoGeometry.Topology.CuntzO2Carrier.S_left C) - star (InfoGeometry.Topology.CuntzO2Carrier.S_left C) * InfoGeometry.Topology.CuntzO2Carrier.S_left C ≠ 0 := by
  have h1 : rangeProjection InfoGeometry.Topology.CuntzO2Carrier.S_left C ≠ 1 := h_mismatch
  exact isometry_branch_commutator_ne_zero (InfoGeometry.Topology.CuntzO2Carrier.S_left C) (InfoGeometry.Topology.CuntzO2Carrier.left_isometry C) h1

/-- Right Cuntz branch commutator is genuinely non-zero when the right projection is strictly less than 1. -/
theorem right_cuntz_branch_commutator_ne_zero
    (h_mismatch : InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection C ≠ 1) :
    InfoGeometry.Topology.CuntzO2Carrier.S_right C * star (InfoGeometry.Topology.CuntzO2Carrier.S_right C) - star (InfoGeometry.Topology.CuntzO2Carrier.S_right C) * InfoGeometry.Topology.CuntzO2Carrier.S_right C ≠ 0 := by
  have h1 : rangeProjection InfoGeometry.Topology.CuntzO2Carrier.S_right C ≠ 1 := h_mismatch
  exact isometry_branch_commutator_ne_zero (InfoGeometry.Topology.CuntzO2Carrier.S_right C) (InfoGeometry.Topology.CuntzO2Carrier.right_isometry C) h1

/-- The left Cuntz range projection is nonzero. -/
theorem left_cuntz_rangeProjection_ne_zero
    [Nontrivial A] :
    InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection C ≠ 0 := by
  unfold InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection
  exact isometry_rangeProjection_ne_zero (InfoGeometry.Topology.CuntzO2Carrier.S_left C) (InfoGeometry.Topology.CuntzO2Carrier.left_isometry C)

/-- The right Cuntz range projection is nonzero. -/
theorem right_cuntz_rangeProjection_ne_zero
    [Nontrivial A] :
    InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection C ≠ 0 := by
  unfold InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection
  exact isometry_rangeProjection_ne_zero (InfoGeometry.Topology.CuntzO2Carrier.S_right C) (InfoGeometry.Topology.CuntzO2Carrier.right_isometry C)

/-- The left Cuntz range projection cannot be the unit, because the right branch
is nonzero and the two branches sum to the unit. -/
theorem left_cuntz_rangeProjection_ne_one_of_right_ne_zero
    (h_right_nonzero : InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection C ≠ 0) :
    InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection C ≠ 1 := by
  intro hleft
  have hsum : (1 : A) + InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection C = 1 := by
    simpa [hleft] using InfoGeometry.Topology.CuntzO2Carrier.rangeProjection_sum_one C
  have hright0 : InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection C = 0 := by
    have hsum' : (1 : A) + InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection C = (1 : A) + 0 := by
      simpa using hsum
    exact add_left_cancel hsum'
  exact h_right_nonzero hright0

/-- The right Cuntz range projection cannot be the unit, because the left branch
is nonzero and the two branches sum to the unit. -/
theorem right_cuntz_rangeProjection_ne_one_of_left_ne_zero
    (h_left_nonzero : InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection C ≠ 0) :
    InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection C ≠ 1 := by
  intro hright
  have hsum : InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection C + (1 : A) = 1 := by
    simpa [hright] using InfoGeometry.Topology.CuntzO2Carrier.rangeProjection_sum_one C
  have hleft0 : InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection C = 0 := by
    have hsum' : InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection C + (1 : A) = 0 + (1 : A) := by
      simpa using hsum
    exact add_right_cancel hsum'
  exact h_left_nonzero hleft0

/-- The left Cuntz range projection cannot be the unit in a nontrivial ring. -/
theorem left_cuntz_rangeProjection_ne_one
    [Nontrivial A] :
    InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection C ≠ 1 :=
  left_cuntz_rangeProjection_ne_one_of_right_ne_zero C
    (right_cuntz_rangeProjection_ne_zero (C := C))

/-- The right Cuntz range projection cannot be the unit in a nontrivial ring. -/
theorem right_cuntz_rangeProjection_ne_one
    [Nontrivial A] :
    InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection C ≠ 1 :=
  right_cuntz_rangeProjection_ne_one_of_left_ne_zero C
    (left_cuntz_rangeProjection_ne_zero (C := C))

/-- Left Cuntz branch commutator is genuinely non-zero if the opposite branch is nonzero. -/
theorem left_cuntz_branch_commutator_ne_zero_of_right_ne_zero
    (h_right_nonzero : InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection C ≠ 0) :
    InfoGeometry.Topology.CuntzO2Carrier.S_left C * star (InfoGeometry.Topology.CuntzO2Carrier.S_left C) - star (InfoGeometry.Topology.CuntzO2Carrier.S_left C) * InfoGeometry.Topology.CuntzO2Carrier.S_left C ≠ 0 := by
  exact isometry_branch_commutator_ne_zero (InfoGeometry.Topology.CuntzO2Carrier.S_left C) (InfoGeometry.Topology.CuntzO2Carrier.left_isometry C)
    (left_cuntz_rangeProjection_ne_one_of_right_ne_zero C h_right_nonzero)

/-- Right Cuntz branch commutator is genuinely non-zero if the opposite branch is nonzero. -/
theorem right_cuntz_branch_commutator_ne_zero_of_left_ne_zero
    (h_left_nonzero : InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection C ≠ 0) :
    InfoGeometry.Topology.CuntzO2Carrier.S_right C * star (InfoGeometry.Topology.CuntzO2Carrier.S_right C) - star (InfoGeometry.Topology.CuntzO2Carrier.S_right C) * InfoGeometry.Topology.CuntzO2Carrier.S_right C ≠ 0 := by
  exact isometry_branch_commutator_ne_zero (InfoGeometry.Topology.CuntzO2Carrier.S_right C) (InfoGeometry.Topology.CuntzO2Carrier.right_isometry C)
    (right_cuntz_rangeProjection_ne_one_of_left_ne_zero C h_left_nonzero)

/-- Left Cuntz branch commutator is genuinely non-zero without an extra
mismatch property in a nontrivial ring, because the left range projection cannot be the unit. -/
theorem left_cuntz_branch_commutator_ne_zero'
    [Nontrivial A] :
    InfoGeometry.Topology.CuntzO2Carrier.S_left C * star (InfoGeometry.Topology.CuntzO2Carrier.S_left C) - star (InfoGeometry.Topology.CuntzO2Carrier.S_left C) * InfoGeometry.Topology.CuntzO2Carrier.S_left C ≠ 0 := by
  exact isometry_branch_commutator_ne_zero (InfoGeometry.Topology.CuntzO2Carrier.S_left C) (InfoGeometry.Topology.CuntzO2Carrier.left_isometry C)
    (left_cuntz_rangeProjection_ne_one (C := C))

/-- Right Cuntz branch commutator is genuinely non-zero without an extra
mismatch property in a nontrivial ring, because the right range projection cannot be the unit. -/
theorem right_cuntz_branch_commutator_ne_zero'
    [Nontrivial A] :
    InfoGeometry.Topology.CuntzO2Carrier.S_right C * star (InfoGeometry.Topology.CuntzO2Carrier.S_right C) - star (InfoGeometry.Topology.CuntzO2Carrier.S_right C) * InfoGeometry.Topology.CuntzO2Carrier.S_right C ≠ 0 := by
  exact isometry_branch_commutator_ne_zero (InfoGeometry.Topology.CuntzO2Carrier.S_right C) (InfoGeometry.Topology.CuntzO2Carrier.right_isometry C)
    (right_cuntz_rangeProjection_ne_one (C := C))

end InfoGeometry.Canonical.DeformedIdeleAction

end noncomputable section
