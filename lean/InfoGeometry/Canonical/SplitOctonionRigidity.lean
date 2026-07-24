import Mathlib.Algebra.Ring.Associator
import Mathlib.Tactic

/-!
# Split-Octonion Rigidity

This module records the theorem form of the non-scalar rigidity statement.

It does **not** claim a concrete octonion classification theorem, an
automorphism-group identification, or a split-octonion multiplication table.
Instead, it packages the logical consequence of two scalar-collapse axioms:

* if the commutant collapses to scalars, then a non-scalar element has a
  nonzero commutator defect;
* if the left nucleus collapses to scalars, then a non-scalar element has a
  nonzero associator defect.

The two defects are allowed to be different.
-/

noncomputable section

namespace InfoGeometry.Canonical.SplitOctonionRigidity

section AbstractRigidity

variable {R O : Type*} [CommSemiring R] [NonUnitalNonAssocRing O] [Module R O] [One O]

/-- The commutator `[x,y] = xy - yx`. -/
def commutator (x y : O) : O :=
  x * y - y * x

/-- The associator `(x,y,z) = (xy)z - x(yz)`. -/
def associator (x y z : O) : O :=
  (x * y) * z - x * (y * z)

/-- Scalar elements are exactly the scalar multiples of `1`. -/
def IsScalar (x : O) : Prop :=
  ∃ r : R, x = r • (1 : O)

/-- A non-scalar element has a nonzero commutator defect. -/
lemma exists_nonzero_commutator_of_not_scalar
    (hcomm : ∀ x : O, (∀ y : O, commutator (O := O) x y = 0) → IsScalar (R := R) x)
    {x : O}
    (hx : ¬ IsScalar (R := R) x) :
    ∃ y : O, commutator (O := O) x y ≠ 0 := by
  by_contra h
  have hzero : ∀ y : O, commutator (O := O) x y = 0 := by
    intro y
    by_contra hy
    exact h ⟨y, hy⟩
  exact hx (hcomm x hzero)

/-- A non-scalar element has a nonzero associator defect. -/
lemma exists_nonzero_associator_of_not_scalar
    (hnuc : ∀ x : O, (∀ y z : O, associator (O := O) x y z = 0) → IsScalar (R := R) x)
    {x : O}
    (hx : ¬ IsScalar (R := R) x) :
    ∃ y z : O, associator (O := O) x y z ≠ 0 := by
  by_contra h
  have hzero : ∀ y z : O, associator (O := O) x y z = 0 := by
    intro y z
    by_contra hyz
    exact h ⟨y, z, hyz⟩
  exact hx (hnuc x hzero)

/--
Safe theorem:
the two defects need not use the same element.
-/
lemma non_scalar_has_nonzero_commutator_and_associator
    (hcomm : ∀ x : O, (∀ y : O, commutator (O := O) x y = 0) → IsScalar (R := R) x)
    (hnuc : ∀ x : O, (∀ y z : O, associator (O := O) x y z = 0) → IsScalar (R := R) x)
    {x : O}
    (hx : ¬ IsScalar (R := R) x) :
    (∃ y : O, commutator (O := O) x y ≠ 0)
      ∧ (∃ y z : O, associator (O := O) x y z ≠ 0) := by
  exact ⟨exists_nonzero_commutator_of_not_scalar (R := R) (O := O) hcomm hx,
         exists_nonzero_associator_of_not_scalar (R := R) (O := O) hnuc hx⟩

end AbstractRigidity

end InfoGeometry.Canonical.SplitOctonionRigidity
