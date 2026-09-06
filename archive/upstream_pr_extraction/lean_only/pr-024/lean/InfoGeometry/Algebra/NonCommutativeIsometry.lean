import Mathlib

/-!
# Non-Commutative Isometry

This module owns the finite algebraic statement that an isometry with a
proper range projection has a nonzero commutator with its adjoint.

#### BUCKET 1: CLOSED FINITE THEOREMS
Generic source/range commutator identities, nonzero commutator under an
explicit range/unit mismatch, idempotence of source/range projections under
explicit partial-isometry hypotheses, and vanishing for a two-sided inverse.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
The nonzero commutator theorem depends only on the named isometry premise
`star S * S = 1` and the named mismatch premise `rangeProjection S ≠ 1`.
The idempotence theorems depend only on explicit partial-isometry premises.

#### BUCKET 3: OPEN CLOSURE DEBT
No C*-completion, topology, torsion, anomaly, idelic, q-deformation, KMS,
or spectral consequence is asserted here.
-/

noncomputable section

namespace InfoGeometry.Algebra.NonCommutativity

variable {A : Type*} [Ring A] [StarRing A]

/-! ## One-branch finite algebra -/

/-- Range projection expression associated to a branch operator. -/
def rangeProjection (S : A) : A :=
  S * star S

/-- Source projection expression associated to a branch operator. -/
def sourceProjection (S : A) : A :=
  star S * S

/-!
The commutator of a branch operator with its adjoint is exactly the range
projection minus the source projection.
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

/--
An isometry has a genuinely nonzero branch commutator whenever its range
projection is not the unit.
-/
theorem isometry_branch_commutator_ne_zero
    (S : A) (hS : star S * S = 1)
    (hRange : rangeProjection S ≠ (1 : A)) :
    S * star S - star S * S ≠ 0 := by
  rw [isometry_branch_commutator_eq_range_sub_one S hS]
  intro h
  exact hRange (sub_eq_zero.mp h)

/-- The range projection of a partial isometry is idempotent. -/
theorem rangeProjection_idempotent_of_partial_isometry
    (S : A) (hS : S * star S * S = S) :
    rangeProjection S * rangeProjection S = rangeProjection S := by
  unfold rangeProjection
  calc
    (S * star S) * (S * star S) = (S * star S * S) * star S := by
      simp only [mul_assoc]
    _ = S * star S := by rw [hS]

/-- The source projection of a partial isometry is idempotent. -/
theorem sourceProjection_idempotent_of_partial_isometry
    (S : A) (hS : star S * S * star S = star S) :
    sourceProjection S * sourceProjection S = sourceProjection S := by
  unfold sourceProjection
  calc
    (star S * S) * (star S * S) = (star S * S * star S) * S := by
      simp only [mul_assoc]
    _ = star S * S := by rw [hS]

/-- A two-sided inverse collapses the finite commutator to zero. -/
theorem two_sided_inverse_branch_commutator_zero
    (S : A) (h_left : star S * S = 1) (h_right : S * star S = 1) :
    S * star S - star S * S = 0 := by
  rw [h_left, h_right]
  exact sub_self 1

end InfoGeometry.Algebra.NonCommutativity

end noncomputable section
