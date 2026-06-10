import InfoGeometry.Canonical.CantorBoundaryCuntzShift

/-!
# Deformed Idele Action: finite Cuntz readout

This module formalizes the finite algebraic readout behind the phrase
"deformed idelic action".

The closed theorem surface is deliberately narrow:

* a branch operator `S` has a range projection `S * S*`;
* a branch operator has a source projection `S* * S`;
* the commutator `S * S* - S* * S` is exactly
  `rangeProjection S - sourceProjection S`;
* when `S` is an isometry (`S* * S = 1`), this specializes to
  `rangeProjection S - 1`;
* the existing `CuntzO2Carrier` supplies this isometry premise for its left and
  right branches.

No theorem here asserts an adele/idele group, a quantum torus, q-deformation,
Souriau flow, KMS transition, root-of-unity braid representation, Galois action,
C*-completion, zeta theorem, or RH consequence.

#### BUCKET 1: CLOSED FINITE THEOREMS
Generic source/range commutator identities, source/range idempotence under
explicit partial-isometry premises, and Cuntz-branch specializations.

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

variable {A : Type*} [Ring A] [StarRing A]

/-! ## One-branch finite algebra -/

/-- Range projection expression associated to a branch operator. -/
def rangeProjection (S : A) : A :=
  S * star S

/-- Source projection expression associated to a branch operator. -/
def sourceProjection (S : A) : A :=
  star S * S

/--
Finite deformed-translation commutator readout.

This is just the transparent algebraic identity that separates the range and
source projections of a branch operator.
-/
theorem branch_commutator_eq_range_sub_source (S : A) :
    S * star S - star S * S = rangeProjection S - sourceProjection S := by
  rfl

/--
If the branch is an isometry (`S* S = 1`), the commutator is range projection
minus the unit.
-/
theorem isometry_branch_commutator_eq_range_sub_one
    (S : A) (hS : star S * S = 1) :
    S * star S - star S * S = rangeProjection S - 1 := by
  unfold rangeProjection
  rw [hS]

/-- The range projection of a partial isometry is idempotent. -/
theorem rangeProjection_idempotent_of_partial_isometry
    (S : A) (hS : S * star S * S = S) :
    rangeProjection S * rangeProjection S = rangeProjection S := by
  unfold rangeProjection
  calc
    (S * star S) * (S * star S) = (S * star S * S) * star S := by
      noncomm_ring
    _ = S * star S := by rw [hS]

/-- The source projection of a partial isometry is idempotent. -/
theorem sourceProjection_idempotent_of_partial_isometry
    (S : A) (hS : star S * S * star S = star S) :
    sourceProjection S * sourceProjection S = sourceProjection S := by
  unfold sourceProjection
  calc
    (star S * S) * (star S * S) = (star S * S * star S) * S := by
      noncomm_ring
    _ = star S * S := by rw [hS]

/-- A two-sided inverse collapses the finite commutator to zero. -/
theorem two_sided_inverse_branch_commutator_zero
    (S : A) (h_left : star S * S = 1) (h_right : S * star S = 1) :
    S * star S - star S * S = 0 := by
  rw [h_left, h_right]
  exact sub_self 1

/-! ## Cuntz `O₂` branch specializations -/

variable (C : CuntzO2Carrier A)

/-- Left Cuntz branch commutator readout. -/
theorem left_cuntz_branch_commutator :
    C.S_left * star C.S_left - star C.S_left * C.S_left =
      C.leftRangeProjection - 1 := by
  unfold CuntzO2Carrier.leftRangeProjection
  exact isometry_branch_commutator_eq_range_sub_one C.S_left C.left_isometry

/-- Right Cuntz branch commutator readout. -/
theorem right_cuntz_branch_commutator :
    C.S_right * star C.S_right - star C.S_right * C.S_right =
      C.rightRangeProjection - 1 := by
  unfold CuntzO2Carrier.rightRangeProjection
  exact isometry_branch_commutator_eq_range_sub_one C.S_right C.right_isometry

/-- Left Cuntz branch range projection is idempotent. -/
theorem left_cuntz_rangeProjection_idempotent :
    C.leftRangeProjection * C.leftRangeProjection = C.leftRangeProjection :=
  C.leftRangeProjection_idempotent

/-- Right Cuntz branch range projection is idempotent. -/
theorem right_cuntz_rangeProjection_idempotent :
    C.rightRangeProjection * C.rightRangeProjection = C.rightRangeProjection :=
  C.rightRangeProjection_idempotent

/-- The two Cuntz range projections form a finite branch partition. -/
theorem cuntz_branch_partition :
    C.leftRangeProjection + C.rightRangeProjection = 1 :=
  C.rangeProjection_sum_one

end InfoGeometry.Canonical.DeformedIdeleAction

end noncomputable section
