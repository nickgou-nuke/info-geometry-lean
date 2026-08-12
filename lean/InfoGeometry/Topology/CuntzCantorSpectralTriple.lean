import Mathlib.Tactic
import Mathlib.Order.Quotient
import InfoGeometry.OperatorAlgebra.ErlangenNet
import InfoGeometry.OperatorAlgebra.SpectralTriple
import InfoGeometry.Canonical.BilingualRealHestenesDictionary
import InfoGeometry.Canonical.HestenesRealStructures
import InfoGeometry.Meta.Architecture
import InfoGeometry.Algebra.CuntzN

open scoped InnerProductSpace

noncomputable section

namespace InfoGeometry.Topology

open InfoGeometry.Krein

/-!
# Cuntz/Cantor bounded resolvent packet

This file gives a bounded operator packet for the symbolic binary boundary of
`ErlangenNet`.

The module deliberately separates four layers:

* a binary symbolic boundary `N -> BinarySector`;
* Cuntz `O_2`-style isometry data on an abstract star algebra;
* candidate Majorana/Clifford operators built from shifts;
* a property-gated bounded resolvent packet.

Guardrail: the Cuntz relations alone do not prove that `S + S*` is a Clifford
unitary. The CAR/Clifford laws therefore require explicit hypotheses.
Likewise, the bounded operator, resolvent identities, compactness property,
and dimension readout are supplied as data, not derived from the Cuntz carrier
alone. The compact-resolvent theorem below records the resulting
finite-dimensional obstruction.
-/

open InfoGeometry.OperatorAlgebra.ErlangenNet

/-- Prefixing a binary symbol to an infinite Cantor code. -/
@[rep_depth operator]
def prefixBoundary (s : BinarySector) (x : (ℕ → BinarySector)) : (ℕ → BinarySector)
    | 0 => s
    | n + 1 => x n

@[rep_depth operator]
theorem prefixBoundary_zero
    (s : BinarySector) (x : (ℕ → BinarySector)) :
    prefixBoundary s x 0 = s :=
  rfl

@[rep_depth operator]
theorem prefixBoundary_succ
    (s : BinarySector) (x : (ℕ → BinarySector)) (n : Nat) :
    prefixBoundary s x (n + 1) = x n :=
  rfl

namespace CuntzO2Carrier

variable {Op : Type*} [Ring Op] [StarRing Op]
variable (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op)

/-- The left branch is the canonical zero-indexed Cuntz generator. -/
@[rep_depth operator]
def S_left : Op := C.S 0

/-- The right branch is the canonical one-indexed Cuntz generator. -/
@[rep_depth operator]
def S_right : Op := C.S 1

theorem left_isometry : star (CuntzO2Carrier.S_left C) * (CuntzO2Carrier.S_left C) = 1 := by
  simpa [S_left] using C.isometry 0 0

theorem right_isometry : star (CuntzO2Carrier.S_right C) * (CuntzO2Carrier.S_right C) = 1 := by
  simpa [S_right] using C.isometry 1 1

theorem orthogonal_ranges :
    star (CuntzO2Carrier.S_left C) * (CuntzO2Carrier.S_right C) = 0 ∧ star (CuntzO2Carrier.S_right C) * (CuntzO2Carrier.S_left C) = 0 := by
  constructor
  · simpa [S_left, S_right] using C.isometry 0 1
  · simpa [S_left, S_right] using C.isometry 1 0

theorem range_sum :
    (CuntzO2Carrier.S_left C) * star (CuntzO2Carrier.S_left C) + (CuntzO2Carrier.S_right C) * star (CuntzO2Carrier.S_right C) = 1 := by
  simpa [S_left, S_right] using
    C.range_sum

/-- Left range projection `S_1 S_1*`. -/
@[rep_depth operator]
def leftRangeProjection : Op :=
  (CuntzO2Carrier.S_left C) * star (CuntzO2Carrier.S_left C)

/-- Right range projection `S_2 S_2*`. -/
@[rep_depth operator]
def rightRangeProjection : Op :=
  (CuntzO2Carrier.S_right C) * star (CuntzO2Carrier.S_right C)

/-- The two range projections sum to the identity by the Cuntz relation. -/
@[rep_depth operator]
theorem rangeProjection_sum_one :
    (leftRangeProjection C) + (rightRangeProjection C) = 1 := by
  exact range_sum C

theorem leftRangeProjection_star :
    star (leftRangeProjection C) = (leftRangeProjection C) := by
  unfold leftRangeProjection
  rw [star_mul, star_star]

theorem rightRangeProjection_star :
    star (rightRangeProjection C) = (rightRangeProjection C) := by
  unfold rightRangeProjection
  rw [star_mul, star_star]

theorem leftRangeProjection_murray_von_neumann_one :
    ∃ v : Op,
      star v * v = 1 ∧
        v * star v = leftRangeProjection C := by
  refine ⟨CuntzO2Carrier.S_left C, left_isometry C, ?_⟩
  rfl

theorem rightRangeProjection_murray_von_neumann_one :
    ∃ v : Op,
      star v * v = 1 ∧
        v * star v = rightRangeProjection C := by
  refine ⟨CuntzO2Carrier.S_right C, right_isometry C, ?_⟩
  rfl

section ProjectionSubequiv

variable {Op : Type*} [Ring Op]

/--
Projection subequivalence on the current Cuntz carrier.

This is the smallest order-theoretic relation we can state without building a
an analytic Cuntz semigroup quotient.
-/
@[rep_depth operator]
def idempotentAbsorption (p q : Op) : Prop :=
  p * q = p

/-- A projection is subequivalent to itself when it is idempotent. -/
@[rep_depth operator]
theorem idempotentAbsorption_refl
    (p : Op) (hp : p * p = p) :
    idempotentAbsorption p p := by
  exact hp

/-- Transitivity of projection subequivalence. -/
@[rep_depth operator]
theorem idempotentAbsorption_trans
    {p q r : Op}
    (hpq : idempotentAbsorption p q)
    (hqr : idempotentAbsorption q r) :
    idempotentAbsorption p r := by
  calc
    p * r = (p * q) * r := by
      rw [hpq]
    _ = p * (q * r) := by
      rw [mul_assoc]
    _ = p * q := by
      rw [hqr]
    _ = p := by
      rw [hpq]

end ProjectionSubequiv

/-- The left Cuntz range projection is subequivalent to the unit. -/
@[rep_depth operator]
theorem leftRangeProjection_subequiv_one :
    idempotentAbsorption (leftRangeProjection C) 1 := by
  unfold idempotentAbsorption
  simp

/-- The right Cuntz range projection is subequivalent to the unit. -/
@[rep_depth operator]
theorem rightRangeProjection_subequiv_one :
    idempotentAbsorption (rightRangeProjection C) 1 := by
  unfold idempotentAbsorption
  simp

/-- The left range projection is subequivalent to itself. -/
@[rep_depth operator]
theorem leftRangeProjection_subequiv_self :
    idempotentAbsorption (leftRangeProjection C) (leftRangeProjection C) := by
  unfold idempotentAbsorption leftRangeProjection
  calc
    ((CuntzO2Carrier.S_left C) * star (CuntzO2Carrier.S_left C)) * ((CuntzO2Carrier.S_left C) * star (CuntzO2Carrier.S_left C))
        = (CuntzO2Carrier.S_left C) * (star (CuntzO2Carrier.S_left C) * (CuntzO2Carrier.S_left C)) * star (CuntzO2Carrier.S_left C) := by
            noncomm_ring
    _ = (CuntzO2Carrier.S_left C) * 1 * star (CuntzO2Carrier.S_left C) := by
          rw [left_isometry C]
    _ = (CuntzO2Carrier.S_left C) * star (CuntzO2Carrier.S_left C) := by
          simp

/-- The right range projection is subequivalent to itself. -/
@[rep_depth operator]
theorem rightRangeProjection_subequiv_self :
    idempotentAbsorption (rightRangeProjection C) (rightRangeProjection C) := by
  unfold idempotentAbsorption rightRangeProjection
  calc
    ((CuntzO2Carrier.S_right C) * star (CuntzO2Carrier.S_right C)) * ((CuntzO2Carrier.S_right C) * star (CuntzO2Carrier.S_right C))
        = (CuntzO2Carrier.S_right C) * (star (CuntzO2Carrier.S_right C) * (CuntzO2Carrier.S_right C)) * star (CuntzO2Carrier.S_right C) := by
            noncomm_ring
    _ = (CuntzO2Carrier.S_right C) * 1 * star (CuntzO2Carrier.S_right C) := by
          rw [right_isometry C]
    _ = (CuntzO2Carrier.S_right C) * star (CuntzO2Carrier.S_right C) := by
          simp

/--
Absorption of the left range projection by the Cuntz partition of unity.

This is the first order-theoretic readout for the Cuntz carrier.
-/
@[rep_depth operator]
theorem leftRangeProjection_absorb_sum_one :
    (leftRangeProjection C) * (leftRangeProjection C + (rightRangeProjection C))
      = (leftRangeProjection C) := by
  calc
    (leftRangeProjection C) * (leftRangeProjection C + (rightRangeProjection C))
        = (leftRangeProjection C) * 1 := by
            rw [rangeProjection_sum_one C]
    _ = (leftRangeProjection C) := by
          rw [mul_one]

/--
Absorption of the right range projection by the Cuntz partition of unity.

This is the symmetric order-theoretic readout for the Cuntz carrier.
-/
@[rep_depth operator]
theorem rightRangeProjection_absorb_sum_one :
    (rightRangeProjection C) * (leftRangeProjection C + (rightRangeProjection C))
      = (rightRangeProjection C) := by
  calc
    (rightRangeProjection C) * (leftRangeProjection C + (rightRangeProjection C))
        = (rightRangeProjection C) * 1 := by
            rw [rangeProjection_sum_one C]
    _ = (rightRangeProjection C) := by
          rw [mul_one]

/--
First-level Cuntz decomposition on the operator carrier.

Any element splits into its left and right branch components under the Cuntz
range projections.
-/
@[rep_depth operator]
theorem rangeProjection_decomposition (x : Op) :
    (leftRangeProjection C) * x + (rightRangeProjection C) * x = x := by
  calc
    (leftRangeProjection C) * x + (rightRangeProjection C) * x
        = (leftRangeProjection C + (rightRangeProjection C)) * x := by
            rw [add_mul]
    _ = x := by
          rw [rangeProjection_sum_one C, one_mul]

/--
Right-first decomposition of the operator carrier by the Cuntz range
projections.
-/
@[rep_depth operator]
theorem rangeProjection_decomposition_right (x : Op) :
    x * (leftRangeProjection C) + x * (rightRangeProjection C) = x := by
  calc
    x * (leftRangeProjection C) + x * (rightRangeProjection C)
        = x * (leftRangeProjection C + (rightRangeProjection C)) := by
            rw [mul_add]
    _ = x := by
          rw [rangeProjection_sum_one C, mul_one]

/-- Left range projection is idempotent. -/
@[rep_depth operator]
theorem leftRangeProjection_idempotent :
    (leftRangeProjection C) * (leftRangeProjection C) = (leftRangeProjection C) := by
  unfold leftRangeProjection
  calc
    ((CuntzO2Carrier.S_left C) * star (CuntzO2Carrier.S_left C)) * ((CuntzO2Carrier.S_left C) * star (CuntzO2Carrier.S_left C))
        = (CuntzO2Carrier.S_left C) * (star (CuntzO2Carrier.S_left C) * (CuntzO2Carrier.S_left C)) * star (CuntzO2Carrier.S_left C) := by
          noncomm_ring
    _ = (CuntzO2Carrier.S_left C) * 1 * star (CuntzO2Carrier.S_left C) := by
          rw [left_isometry C]
    _ = (CuntzO2Carrier.S_left C) * star (CuntzO2Carrier.S_left C) := by
          simp

/-- Right range projection is idempotent. -/
@[rep_depth operator]
theorem rightRangeProjection_idempotent :
    (rightRangeProjection C) * (rightRangeProjection C) = (rightRangeProjection C) := by
  unfold rightRangeProjection
  calc
    ((CuntzO2Carrier.S_right C) * star (CuntzO2Carrier.S_right C)) * ((CuntzO2Carrier.S_right C) * star (CuntzO2Carrier.S_right C))
        = (CuntzO2Carrier.S_right C) * (star (CuntzO2Carrier.S_right C) * (CuntzO2Carrier.S_right C)) * star (CuntzO2Carrier.S_right C) := by
          noncomm_ring
    _ = (CuntzO2Carrier.S_right C) * 1 * star (CuntzO2Carrier.S_right C) := by
          rw [right_isometry C]
    _ = (CuntzO2Carrier.S_right C) * star (CuntzO2Carrier.S_right C) := by
          simp

theorem leftRangeProjection_is_star_projection :
    (leftRangeProjection C) * (leftRangeProjection C) = leftRangeProjection C ∧
      star (leftRangeProjection C) = leftRangeProjection C := by
  exact ⟨leftRangeProjection_idempotent (C := C),
    leftRangeProjection_star (C := C)⟩

theorem rightRangeProjection_is_star_projection :
    (rightRangeProjection C) * (rightRangeProjection C) = rightRangeProjection C ∧
      star (rightRangeProjection C) = rightRangeProjection C := by
  exact ⟨rightRangeProjection_idempotent (C := C),
    rightRangeProjection_star (C := C)⟩

/--
Idempotent elements of the Cuntz carrier, packaged as a concrete subtype.

This carrier does not require self-adjointness. Star projections are handled
by the separate `IsStarProjection` theorems below.
-/
@[rep_depth operator]
def CuntzIdempotent := { p : Op // p * p = p }

namespace CuntzIdempotent

variable {Op : Type*} [Ring Op]

/-- The idempotence proof of a Cuntz idempotent. -/
@[rep_depth operator]
theorem isIdempotent (p : CuntzIdempotent (Op := Op)) :
    p.1 * p.1 = p.1 := p.2

end CuntzIdempotent

/-- Lift a Cuntz carrier range projection to the projection subtype. -/
@[rep_depth operator]
def leftCuntzIdempotent :
    CuntzIdempotent (Op := Op) where
  val := (leftRangeProjection C)
  property := leftRangeProjection_idempotent (C := C)

/-- Lift the right Cuntz range projection to the projection subtype. -/
@[rep_depth operator]
def rightCuntzIdempotent :
    CuntzIdempotent (Op := Op) where
  val := (rightRangeProjection C)
  property := rightRangeProjection_idempotent (C := C)

section IdempotentPreorder

variable {Op : Type*} [Ring Op]

/--
Absorption between Cuntz idempotents.

This relation is not Murray--von Neumann equivalence and does not define the
analytic Cuntz semigroup.
-/
@[rep_depth operator]
def idempotentPreorder (p q : CuntzIdempotent (Op := Op)) : Prop :=
  idempotentAbsorption p.1 q.1

/-- Reflexivity of the idempotent absorption preorder. -/
@[rep_depth operator]
theorem idempotentPreorder_refl (p : CuntzIdempotent (Op := Op)) :
    idempotentPreorder p p := by
  exact idempotentAbsorption_refl p.1 p.2

/-- Transitivity of the idempotent absorption preorder. -/
@[rep_depth operator]
theorem idempotentPreorder_trans
    {p q r : CuntzIdempotent (Op := Op)}
    (hpq : idempotentPreorder p q)
    (hqr : idempotentPreorder q r) :
    idempotentPreorder p r := by
  exact idempotentAbsorption_trans hpq hqr

end IdempotentPreorder

/-- The idempotent absorption relation is the native preorder here. -/
@[rep_depth operator]
instance instLE : LE (CuntzIdempotent (Op := Op)) where
  le p q := idempotentPreorder p q

/-- The idempotent absorption relation is reflexive and transitive. -/
@[rep_depth operator]
instance instPreorder : Preorder (CuntzIdempotent (Op := Op)) where
  le_refl := idempotentPreorder_refl
  le_trans := by
    intro a b c hab hbc
    exact idempotentPreorder_trans (p := a) (q := b) (r := c) hab hbc

/-- The unit element as a Cuntz idempotent. -/
@[rep_depth operator]
def unitCuntzIdempotent : CuntzIdempotent (Op := Op) where
  val := 1
  property := by
    simp

section ProjectionOrthogonal

variable {Op : Type*} [Ring Op]

/-- The zero element as a Cuntz idempotent. -/
@[rep_depth operator]
def zeroCuntzIdempotent : CuntzIdempotent (Op := Op) where
  val := 0
  property := by
    simp

/--
Orthogonality of Cuntz idempotents.

This is the compatibility property needed to form an additive projection sum.
-/
@[rep_depth operator]
def idempotentOrthogonal (p q : CuntzIdempotent (Op := Op)) : Prop :=
  p.1 * q.1 = 0 ∧ q.1 * p.1 = 0

/-- Zero is orthogonal to every Cuntz idempotent on the left. -/
@[rep_depth operator]
theorem zeroIdempotentOrthogonal_left (p : CuntzIdempotent (Op := Op)) :
    idempotentOrthogonal (zeroCuntzIdempotent (Op := Op)) p := by
  constructor
  · change (0 : Op) * p.1 = 0
    simp
  · change p.1 * (0 : Op) = 0
    simp

/-- Zero is orthogonal to every Cuntz idempotent on the right. -/
@[rep_depth operator]
theorem zeroIdempotentOrthogonal_right (p : CuntzIdempotent (Op := Op)) :
    idempotentOrthogonal p (zeroCuntzIdempotent (Op := Op)) := by
  constructor
  · change p.1 * (0 : Op) = 0
    simp
  · change (0 : Op) * p.1 = 0
    simp

/--
Orthogonal sum of Cuntz idempotents.

This is the first theorem-backed additive operation on the projection carrier.
-/
@[rep_depth operator]
def orthogonalSum
    (p q : CuntzIdempotent (Op := Op))
    (h : idempotentOrthogonal p q) : CuntzIdempotent (Op := Op) where
  val := p.1 + q.1
  property := by
    unfold idempotentOrthogonal at h
    have hpq : p.1 * q.1 = 0 := h.1
    have hqp : q.1 * p.1 = 0 := h.2
    calc
      (p.1 + q.1) * (p.1 + q.1)
          = p.1 * p.1 + p.1 * q.1 + q.1 * p.1 + q.1 * q.1 := by
              noncomm_ring
      _ = p.1 * p.1 + q.1 * q.1 := by simp [hpq, hqp]
      _ = p.1 + q.1 := by
            have hp : p.1 * p.1 = p.1 := p.2
            have hq : q.1 * q.1 = q.1 := q.2
            simp [hp, hq]

theorem orthogonalSum_is_star_projection
    {Op : Type*} [Ring Op] [StarRing Op]
    (p q : CuntzIdempotent (Op := Op))
    (h : idempotentOrthogonal p q)
    (hp : star p.1 = p.1)
    (hq : star q.1 = q.1) :
    (orthogonalSum p q h).1 * (orthogonalSum p q h).1 =
        (orthogonalSum p q h).1 ∧
      star (orthogonalSum p q h).1 = (orthogonalSum p q h).1 := by
  constructor
  · exact (orthogonalSum p q h).2
  · change star (p.1 + q.1) = p.1 + q.1
    rw [star_add, hp, hq]

/-- Orthogonal sum is commutative when the orthogonality data is swapped. -/
@[rep_depth operator]
theorem orthogonalSum_comm
    (p q : CuntzIdempotent (Op := Op))
    (h : idempotentOrthogonal p q) :
    orthogonalSum p q h = orthogonalSum q p ⟨h.2, h.1⟩ := by
  apply Subtype.ext
  change p.1 + q.1 = q.1 + p.1
  simp [add_comm]

/-- Orthogonal sum with zero on the left is the original projection. -/
@[rep_depth operator]
theorem orthogonalSum_zero_left
    (p : CuntzIdempotent (Op := Op)) :
      orthogonalSum (zeroCuntzIdempotent (Op := Op)) p
      (zeroIdempotentOrthogonal_left (p := p)) = p := by
  apply Subtype.ext
  change (0 : Op) + p.1 = p.1
  simp

/-- Orthogonal sum with zero on the right is the original projection. -/
@[rep_depth operator]
theorem orthogonalSum_zero_right
    (p : CuntzIdempotent (Op := Op)) :
      orthogonalSum p (zeroCuntzIdempotent (Op := Op))
      (zeroIdempotentOrthogonal_right (p := p)) = p := by
  apply Subtype.ext
  change p.1 + (0 : Op) = p.1
  simp

/-- The sum of an orthogonal pair is orthogonal to a third projection if each summand is. -/
@[rep_depth operator]
theorem orthogonalSum_right_orthogonal
    (p q r : CuntzIdempotent (Op := Op))
    (hpq : idempotentOrthogonal p q)
    (hpr : idempotentOrthogonal p r)
    (hqr : idempotentOrthogonal q r) :
    idempotentOrthogonal (orthogonalSum p q hpq) r := by
  constructor
  · change (p.1 + q.1) * r.1 = 0
    calc
      (p.1 + q.1) * r.1 = p.1 * r.1 + q.1 * r.1 := by
        rw [add_mul]
      _ = 0 := by
        rw [hpr.1, hqr.1]
        simp
  · change r.1 * (p.1 + q.1) = 0
    calc
      r.1 * (p.1 + q.1) = r.1 * p.1 + r.1 * q.1 := by
        rw [mul_add]
      _ = 0 := by
        rw [hpr.2, hqr.2]
        simp

/-- The sum of a third projection with an orthogonal pair is orthogonal if each summand is. -/
@[rep_depth operator]
theorem orthogonalSum_left_orthogonal
    (p q r : CuntzIdempotent (Op := Op))
    (hpq : idempotentOrthogonal p q)
    (hpr : idempotentOrthogonal p r)
    (hqr : idempotentOrthogonal q r) :
    idempotentOrthogonal p (orthogonalSum q r hqr) := by
  constructor
  · change p.1 * (q.1 + r.1) = 0
    calc
      p.1 * (q.1 + r.1) = p.1 * q.1 + p.1 * r.1 := by
        rw [mul_add]
      _ = 0 := by
        rw [hpq.1, hpr.1]
        simp
  · change (q.1 + r.1) * p.1 = 0
    calc
      (q.1 + r.1) * p.1 = q.1 * p.1 + r.1 * p.1 := by
        rw [add_mul]
      _ = 0 := by
        rw [hpq.2, hpr.2]
        simp

/-- Orthogonal sum is associative on pairwise orthogonal triples. -/
@[rep_depth operator]
theorem orthogonalSum_assoc
    (p q r : CuntzIdempotent (Op := Op))
    (hpq : idempotentOrthogonal p q)
    (hpr : idempotentOrthogonal p r)
    (hqr : idempotentOrthogonal q r) :
    orthogonalSum (orthogonalSum p q hpq) r (orthogonalSum_right_orthogonal p q r hpq hpr hqr) =
      orthogonalSum p (orthogonalSum q r hqr) (orthogonalSum_left_orthogonal p q r hpq hpr hqr) := by
  apply Subtype.ext
  change (p.1 + q.1) + r.1 = p.1 + (q.1 + r.1)
  abel

end ProjectionOrthogonal

/- The left and right range projections are orthogonal on the left product. -/
@[rep_depth operator]
theorem leftRangeProjection_mul_rightRangeProjection_eq_zero :
    (leftRangeProjection C) * (rightRangeProjection C) = 0 := by
  unfold leftRangeProjection rightRangeProjection
  calc
    ((CuntzO2Carrier.S_left C) * star (CuntzO2Carrier.S_left C)) * ((CuntzO2Carrier.S_right C) * star (CuntzO2Carrier.S_right C))
        = (CuntzO2Carrier.S_left C) * (star (CuntzO2Carrier.S_left C) * (CuntzO2Carrier.S_right C)) * star (CuntzO2Carrier.S_right C) := by
          noncomm_ring
    _ = (CuntzO2Carrier.S_left C) * 0 * star (CuntzO2Carrier.S_right C) := by
          rw [(orthogonal_ranges C).1]
    _ = 0 := by
          simp

/-- The left and right range projections are orthogonal on the right product. -/
@[rep_depth operator]
theorem rightRangeProjection_mul_leftRangeProjection_eq_zero :
    (rightRangeProjection C) * (leftRangeProjection C) = 0 := by
  unfold leftRangeProjection rightRangeProjection
  calc
    ((CuntzO2Carrier.S_right C) * star (CuntzO2Carrier.S_right C)) * ((CuntzO2Carrier.S_left C) * star (CuntzO2Carrier.S_left C))
        = (CuntzO2Carrier.S_right C) * (star (CuntzO2Carrier.S_right C) * (CuntzO2Carrier.S_left C)) * star (CuntzO2Carrier.S_left C) := by
          noncomm_ring
    _ = (CuntzO2Carrier.S_right C) * 0 * star (CuntzO2Carrier.S_left C) := by
          rw [(orthogonal_ranges C).2]
    _ = 0 := by
          simp

/-- The left and right Cuntz idempotents are orthogonal. -/
@[rep_depth operator]
theorem leftRightCuntzIdempotent_orthogonal :
    idempotentOrthogonal (leftCuntzIdempotent C) (rightCuntzIdempotent C) := by
  constructor
  · exact leftRangeProjection_mul_rightRangeProjection_eq_zero (C := C)
  · exact rightRangeProjection_mul_leftRangeProjection_eq_zero (C := C)

/-- The left and right Cuntz idempotents sum orthogonally to the unit. -/
@[rep_depth operator]
theorem leftRightOrthogonalSum_eq_unit :
    orthogonalSum (leftCuntzIdempotent C) (rightCuntzIdempotent C)
      (leftRightCuntzIdempotent_orthogonal (C := C)) = unitCuntzIdempotent (Op := Op) := by
  apply Subtype.ext
  change (leftRangeProjection C) + (rightRangeProjection C) = 1
  simpa [leftCuntzIdempotent, rightCuntzIdempotent, unitCuntzIdempotent] using
    rangeProjection_sum_one C

section IdempotentEquivalence

variable {Op : Type*} [Ring Op]

/-- The left summand lies below its orthogonal sum. -/
@[rep_depth operator]
theorem left_le_orthogonalSum
    (p q : CuntzIdempotent (Op := Op))
    (h : idempotentOrthogonal p q) :
    p ≤ orthogonalSum p q h := by
  change p.1 * (p.1 + q.1) = p.1
  have hp : p.1 * p.1 = p.1 := p.2
  have hq : p.1 * q.1 = 0 := h.1
  calc
    p.1 * (p.1 + q.1) = p.1 * p.1 + p.1 * q.1 := by
      rw [mul_add]
    _ = p.1 := by
      rw [hp, hq]
      simp

/-- The right summand lies below its orthogonal sum. -/
@[rep_depth operator]
theorem right_le_orthogonalSum
    (p q : CuntzIdempotent (Op := Op))
    (h : idempotentOrthogonal p q) :
    q ≤ orthogonalSum p q h := by
  change q.1 * (p.1 + q.1) = q.1
  have hq : q.1 * q.1 = q.1 := q.2
  have hpq : q.1 * p.1 = 0 := h.2
  calc
    q.1 * (p.1 + q.1) = q.1 * p.1 + q.1 * q.1 := by
      rw [mul_add]
    _ = q.1 := by
      rw [hpq, hq]
      simp

end IdempotentEquivalence

/-- The left range projection lies below the unit in the projection preorder. -/
@[rep_depth operator]
theorem leftRangeProjection_le_unit :
    leftCuntzIdempotent C ≤ unitCuntzIdempotent (Op := Op) := by
  exact leftRangeProjection_subequiv_one (C := C)

/-- The right range projection lies below the unit in the projection preorder. -/
@[rep_depth operator]
theorem rightRangeProjection_le_unit :
    rightCuntzIdempotent C ≤ unitCuntzIdempotent (Op := Op) := by
  exact rightRangeProjection_subequiv_one (C := C)

section IdempotentEquivalence

variable {Op : Type*} [Ring Op]

/--
Absorption equivalence on Cuntz idempotents.

This is the mutual absorption relation used for the algebraic quotient.
-/
@[rep_depth operator]
def idempotentEquivalent (p q : Op) : Prop :=
  idempotentAbsorption p q ∧ idempotentAbsorption q p

/-- Reflexivity of absorption equivalence on an idempotent. -/
@[rep_depth operator]
theorem idempotentEquivalent_refl
    (p : Op) (hp : p * p = p) :
    idempotentEquivalent p p := by
  constructor
  · exact idempotentAbsorption_refl p hp
  · exact idempotentAbsorption_refl p hp

/-- Symmetry of absorption equivalence. -/
@[rep_depth operator]
theorem idempotentEquivalent_symm
    {p q : Op}
    (hpq : idempotentEquivalent p q) :
    idempotentEquivalent q p := by
  constructor
  · exact hpq.2
  · exact hpq.1

/-- Transitivity of absorption equivalence. -/
@[rep_depth operator]
theorem idempotentEquivalent_trans
    {p q r : Op}
    (hpq : idempotentEquivalent p q)
    (hqr : idempotentEquivalent q r) :
    idempotentEquivalent p r := by
  constructor
  · exact idempotentAbsorption_trans hpq.1 hqr.1
  · exact idempotentAbsorption_trans hqr.2 hpq.2

/-- The orthogonal sum does not depend on the chosen orthogonality proof. -/
@[rep_depth operator]
theorem orthogonalSum_proof_irrel
    (p q : CuntzIdempotent (Op := Op))
    (h h' : idempotentOrthogonal p q) :
    orthogonalSum p q h = orthogonalSum p q h' := by
  apply Subtype.ext
  rfl

/--
Setoid of Cuntz idempotents under the absorption equivalence relation.
-/
@[rep_depth operator]
def CuntzIdempotentSetoid : Setoid (CuntzIdempotent (Op := Op)) where
  r p q := idempotentEquivalent p.1 q.1
  iseqv := by
    constructor
    · intro p
      exact idempotentEquivalent_refl p.1 p.2
    · intro p q h
      exact idempotentEquivalent_symm h
    · intro p q r hpq hqr
      exact idempotentEquivalent_trans hpq hqr

/-- The algebraic quotient carrier generated by the idempotent absorption setoid. -/
@[rep_depth operator]
abbrev IdempotentOrderQuotient := Quotient (CuntzIdempotentSetoid (Op := Op))

/-- The quotient class of an orthogonal sum is independent of the orthogonality property. -/
@[rep_depth operator]
theorem IdempotentOrderQuotient_orthogonalSum_proof_irrel
    (p q : CuntzIdempotent (Op := Op))
    (h h' : idempotentOrthogonal p q) :
    (Quotient.mk (CuntzIdempotentSetoid (Op := Op)) (orthogonalSum p q h) : IdempotentOrderQuotient) =
      Quotient.mk (CuntzIdempotentSetoid (Op := Op)) (orthogonalSum p q h') := by
  rw [orthogonalSum_proof_irrel p q h h']

/--
The idempotent absorption preorder is invariant under absorption equivalence on both sides.
This is the key descent lemma for the quotient carrier.
-/
@[rep_depth operator]
theorem idempotentPreorder_congr
    {p p' q q' : CuntzIdempotent (Op := Op)}
    (hpp' : idempotentEquivalent p.1 p'.val)
    (hqq' : idempotentEquivalent q.1 q'.val) :
    idempotentPreorder p q ↔ idempotentPreorder p' q' := by
  constructor
  · intro hpq
    exact idempotentPreorder_trans (idempotentPreorder_trans hpp'.2 hpq) hqq'.1
  · intro hpq
    exact idempotentPreorder_trans (idempotentPreorder_trans hpp'.1 hpq) hqq'.2

end IdempotentEquivalence

section SelfAdjointIdempotentEquivalence

variable {Op : Type*} [Ring Op] [StarRing Op]

theorem idempotentEquivalent_eq_of_selfAdjoint
    {p q : Op}
    (hps : star p = p)
    (hqs : star q = q)
    (hpq : idempotentEquivalent p q) :
    p = q := by
  have hqp_eq_p : q * p = p := by
    have h := congrArg star hpq.1
    simpa [star_mul, hps, hqs] using h
  have hqp_eq_q : q * p = q := hpq.2
  exact (hqp_eq_q.symm.trans hqp_eq_p).symm

end SelfAdjointIdempotentEquivalence

section IdempotentOrderQuotientOrder

variable {Op : Type*} [Ring Op]

/-- The quotient map to `IdempotentOrderQuotient` is monotone. -/
@[rep_depth operator]
theorem IdempotentOrderQuotient_mk_monotone :
    Monotone (Quotient.mk (CuntzIdempotentSetoid (Op := Op))) :=
  Quotient.mk_monotone (s := CuntzIdempotentSetoid (Op := Op))

/-- The quotient order respects projection preorder on representatives. -/
@[rep_depth operator]
theorem IdempotentOrderQuotient_mk_le
    (p q : CuntzIdempotent (Op := Op))
    (hpq : idempotentPreorder p q) :
    (Quotient.mk (CuntzIdempotentSetoid (Op := Op)) p : IdempotentOrderQuotient) ≤
      Quotient.mk (CuntzIdempotentSetoid (Op := Op)) q :=
  IdempotentOrderQuotient_mk_monotone hpq

/-- Equivalent Cuntz projections define the same quotient class. -/
@[rep_depth operator]
theorem IdempotentOrderQuotient_mk_eq
    {p q : CuntzIdempotent (Op := Op)}
    (hpq : idempotentEquivalent p.1 q.1) :
    (Quotient.mk (CuntzIdempotentSetoid (Op := Op)) p : IdempotentOrderQuotient) =
      Quotient.mk (CuntzIdempotentSetoid (Op := Op)) q := by
  exact Quotient.sound hpq

/-- Equality of quotient classes descends back to projection equivalence. -/
@[rep_depth operator]
theorem IdempotentOrderQuotient_mk_eq_iff
    {p q : CuntzIdempotent (Op := Op)} :
    (Quotient.mk (CuntzIdempotentSetoid (Op := Op)) p : IdempotentOrderQuotient) =
      Quotient.mk (CuntzIdempotentSetoid (Op := Op)) q ↔
      idempotentEquivalent p.1 q.1 := by
  constructor
  · exact Quotient.exact
  · exact IdempotentOrderQuotient_mk_eq

/-- The left summand class lies below the orthogonal sum class. -/
@[rep_depth operator]
theorem IdempotentOrderQuotient_left_le_orthogonalSum
    (p q : CuntzIdempotent (Op := Op))
    (h : idempotentOrthogonal p q) :
    (Quotient.mk (CuntzIdempotentSetoid (Op := Op)) p : IdempotentOrderQuotient) ≤
      Quotient.mk (CuntzIdempotentSetoid (Op := Op)) (orthogonalSum p q h) := by
  exact IdempotentOrderQuotient_mk_le p (orthogonalSum p q h) (left_le_orthogonalSum p q h)

/-- The right summand class lies below the orthogonal sum class. -/
@[rep_depth operator]
theorem IdempotentOrderQuotient_right_le_orthogonalSum
    (p q : CuntzIdempotent (Op := Op))
    (h : idempotentOrthogonal p q) :
    (Quotient.mk (CuntzIdempotentSetoid (Op := Op)) q : IdempotentOrderQuotient) ≤
      Quotient.mk (CuntzIdempotentSetoid (Op := Op)) (orthogonalSum p q h) := by
  exact IdempotentOrderQuotient_mk_le q (orthogonalSum p q h) (right_le_orthogonalSum p q h)

end IdempotentOrderQuotientOrder

/-- The left/right orthogonal sum class is the unit class. -/
@[rep_depth operator]
theorem IdempotentOrderQuotient_leftRightOrthogonalSum_eq_unit :
    (Quotient.mk (CuntzIdempotentSetoid (Op := Op))
      (orthogonalSum (leftCuntzIdempotent C) (rightCuntzIdempotent C)
        (leftRightCuntzIdempotent_orthogonal (C := C))) : IdempotentOrderQuotient) =
      Quotient.mk (CuntzIdempotentSetoid (Op := Op)) (unitCuntzIdempotent (Op := Op)) := by
  rw [leftRightOrthogonalSum_eq_unit]

/-- The left/right orthogonal sum class lies below the unit class. -/
@[rep_depth operator]
theorem IdempotentOrderQuotient_leftRightOrthogonalSum_le_unit :
    (Quotient.mk (CuntzIdempotentSetoid (Op := Op))
      (orthogonalSum (leftCuntzIdempotent C) (rightCuntzIdempotent C)
        (leftRightCuntzIdempotent_orthogonal (C := C))) : IdempotentOrderQuotient) ≤
      Quotient.mk (CuntzIdempotentSetoid (Op := Op)) (unitCuntzIdempotent (Op := Op)) := by
  rw [IdempotentOrderQuotient_leftRightOrthogonalSum_eq_unit]

section IdempotentOrderQuotientOrthogonalSumOrder

variable {Op : Type*} [Ring Op]

/-- The orthogonal sum class lies between the summands and the unit class. -/
@[rep_depth operator]
theorem IdempotentOrderQuotient_orthogonalSum_bounds
    (p q : CuntzIdempotent (Op := Op))
    (h : idempotentOrthogonal p q) :
    (Quotient.mk (CuntzIdempotentSetoid (Op := Op)) p : IdempotentOrderQuotient) ≤
      Quotient.mk (CuntzIdempotentSetoid (Op := Op)) (orthogonalSum p q h) ∧
    (Quotient.mk (CuntzIdempotentSetoid (Op := Op)) q : IdempotentOrderQuotient) ≤
      Quotient.mk (CuntzIdempotentSetoid (Op := Op)) (orthogonalSum p q h) ∧
    (Quotient.mk (CuntzIdempotentSetoid (Op := Op)) (orthogonalSum p q h) : IdempotentOrderQuotient) ≤
      Quotient.mk (CuntzIdempotentSetoid (Op := Op)) (unitCuntzIdempotent (Op := Op)) := by
  constructor
  · exact IdempotentOrderQuotient_left_le_orthogonalSum p q h
  constructor
  · exact IdempotentOrderQuotient_right_le_orthogonalSum p q h
  · exact IdempotentOrderQuotient_mk_le (orthogonalSum p q h) (unitCuntzIdempotent (Op := Op)) (by
      change (orthogonalSum p q h).val * 1 = (orthogonalSum p q h).val
      simp)

/-- The quotient class of an orthogonal sum is independent of the order. -/
@[rep_depth operator]
theorem IdempotentOrderQuotient_orthogonalSum_comm
    (p q : CuntzIdempotent (Op := Op))
    (h : idempotentOrthogonal p q) :
    (Quotient.mk (CuntzIdempotentSetoid (Op := Op)) (orthogonalSum p q h) : IdempotentOrderQuotient) =
      Quotient.mk (CuntzIdempotentSetoid (Op := Op))
        (orthogonalSum q p ⟨h.2, h.1⟩) := by
  rw [orthogonalSum_comm p q h]

/-- The quotient class of an orthogonal sum with zero on the left is the original class. -/
@[rep_depth operator]
theorem IdempotentOrderQuotient_orthogonalSum_zero_left
    (p : CuntzIdempotent (Op := Op)) :
    (Quotient.mk (CuntzIdempotentSetoid (Op := Op))
      (orthogonalSum (zeroCuntzIdempotent (Op := Op)) p
        (zeroIdempotentOrthogonal_left (p := p))) : IdempotentOrderQuotient) =
      Quotient.mk (CuntzIdempotentSetoid (Op := Op)) p := by
  rw [orthogonalSum_zero_left]

/-- The quotient class of an orthogonal sum with zero on the right is the original class. -/
@[rep_depth operator]
theorem IdempotentOrderQuotient_orthogonalSum_zero_right
    (p : CuntzIdempotent (Op := Op)) :
    (Quotient.mk (CuntzIdempotentSetoid (Op := Op))
      (orthogonalSum p (zeroCuntzIdempotent (Op := Op))
        (zeroIdempotentOrthogonal_right (p := p))) : IdempotentOrderQuotient) =
      Quotient.mk (CuntzIdempotentSetoid (Op := Op)) p := by
  rw [orthogonalSum_zero_right]

/-- The quotient class of a pairwise orthogonal triple sum is independent of association. -/
@[rep_depth operator]
theorem IdempotentOrderQuotient_orthogonalSum_assoc
    (p q r : CuntzIdempotent (Op := Op))
    (hpq : idempotentOrthogonal p q)
    (hpr : idempotentOrthogonal p r)
    (hqr : idempotentOrthogonal q r) :
    (Quotient.mk (CuntzIdempotentSetoid (Op := Op))
      (orthogonalSum (orthogonalSum p q hpq) r
        (orthogonalSum_right_orthogonal p q r hpq hpr hqr)) : IdempotentOrderQuotient) =
      Quotient.mk (CuntzIdempotentSetoid (Op := Op))
        (orthogonalSum p (orthogonalSum q r hqr)
          (orthogonalSum_left_orthogonal p q r hpq hpr hqr)) := by
  rw [orthogonalSum_assoc p q r hpq hpr hqr]

end IdempotentOrderQuotientOrthogonalSumOrder


/-- The left Cuntz projection class lies below the unit class. -/
@[rep_depth operator]
theorem leftIdempotentOrderQuotient_le_unit :
    (Quotient.mk (CuntzIdempotentSetoid (Op := Op)) (leftCuntzIdempotent C)) ≤
      Quotient.mk (CuntzIdempotentSetoid (Op := Op)) (unitCuntzIdempotent (Op := Op)) := by
  exact IdempotentOrderQuotient_mk_monotone (leftRangeProjection_le_unit (C := C))

/-- The right Cuntz projection class lies below the unit class. -/
@[rep_depth operator]
theorem rightIdempotentOrderQuotient_le_unit :
    (Quotient.mk (CuntzIdempotentSetoid (Op := Op)) (rightCuntzIdempotent C)) ≤
      Quotient.mk (CuntzIdempotentSetoid (Op := Op)) (unitCuntzIdempotent (Op := Op)) := by
  exact IdempotentOrderQuotient_mk_monotone (rightRangeProjection_le_unit (C := C))

end CuntzO2Carrier

/-!
## Idempotent projector algebra

These are the local algebraic facts used by the sector language.  The first
three hold in any ring.  The Boolean meet/join formulas are stated for
commutative rings, matching the central Cantor-idempotent lane rather than the
noncentral Krein matrix-projection lane.
-/

section IdempotentProjectorAlgebra

variable {R : Type*} [Ring R]

/-- If `e` is idempotent, then `1 - e` is idempotent. -/
@[rep_depth operator]
theorem idempotent_one_sub {e : R} (he : IsIdempotentElem e) :
    IsIdempotentElem (1 - e) :=
  he.one_sub

/-- An idempotent is orthogonal on the right to its complement. -/
@[rep_depth operator]
theorem idempotent_mul_one_sub {e : R} (he : IsIdempotentElem e) :
    e * (1 - e) = 0 := by
  rw [mul_sub, mul_one, he.eq, sub_self]

/-- An idempotent is orthogonal on the left to its complement. -/
@[rep_depth operator]
theorem one_sub_mul_idempotent {e : R} (he : IsIdempotentElem e) :
    (1 - e) * e = 0 := by
  rw [sub_mul, one_mul, he.eq, sub_self]

/-- Product of commuting idempotents is idempotent. -/
@[rep_depth operator]
theorem commuting_idempotent_mul {e f : R}
    (he : IsIdempotentElem e) (hf : IsIdempotentElem f) (hcomm : e * f = f * e) :
    IsIdempotentElem (e * f) := by
  rw [IsIdempotentElem]
  calc
    (e * f) * (e * f) = e * (f * e) * f := by noncomm_ring
    _ = e * (e * f) * f := by rw [hcomm]
    _ = (e * e) * (f * f) := by noncomm_ring
    _ = e * f := by rw [he.eq, hf.eq]

end IdempotentProjectorAlgebra

section CentralIdempotentBooleanAlgebra

variable {R : Type*} [CommRing R]

/-- Boolean meet of central idempotents: multiplication preserves idempotence. -/
@[rep_depth operator]
theorem central_idempotent_boolean_meet {e f : R}
    (he : IsIdempotentElem e) (hf : IsIdempotentElem f) :
    IsIdempotentElem (e * f) := by
  exact commuting_idempotent_mul he hf (mul_comm e f)

/-- Boolean join of central idempotents: `e ∨ f = e + f - e * f`. -/
@[rep_depth operator]
theorem central_idempotent_boolean_join {e f : R}
    (he : IsIdempotentElem e) (hf : IsIdempotentElem f) :
    IsIdempotentElem (e + f - e * f) := by
  have he2 : e ^ 2 = e := by simpa [pow_two] using he.eq
  have hf2 : f ^ 2 = f := by simpa [pow_two] using hf.eq
  rw [IsIdempotentElem]
  ring_nf
  rw [he2, hf2]
  ring

/-- A central idempotent lies below its Boolean join with another central idempotent. -/
@[rep_depth operator]
theorem central_idempotent_boolean_join_absorb_left {e f : R}
    (he : IsIdempotentElem e) (_hf : IsIdempotentElem f) :
    e * (e + f - e * f) = e := by
  have he2 : e ^ 2 = e := by simpa [pow_two] using he.eq
  ring_nf
  rw [he2]
  ring

/-- A central idempotent is absorbed by its Boolean join on the other side too. -/
@[rep_depth operator]
theorem central_idempotent_boolean_join_absorb_right {e f : R}
    (he : IsIdempotentElem e) (_hf : IsIdempotentElem f) :
    (e + f - e * f) * e = e := by
  have he2 : e ^ 2 = e := by simpa [pow_two] using he.eq
  ring_nf
  rw [he2]
  ring

end CentralIdempotentBooleanAlgebra

/-!
## Complete-lattice sector completion

This section records the order-theoretic closure that is already canonical in
mathlib.  It does not assert a full noncommutative projection lattice for an
operator algebra.  Instead it uses concrete sector selections as sets, where
arbitrary joins and meets are the ordinary unions and intersections, refinement
is direct image, coarse-graining is inverse image, and self-similar sectors are
fixed points of a monotone self-map by Knaster--Tarski.
-/

section CompleteLatticeSectorCompletion

universe u v w

/-- Join of finite Cantor/Krein sector selections is union. -/
@[rep_depth operator]
theorem finiteCantorKreinSectorSet_sup_eq_union
    {n : Nat} (P Q : Set ((Fin n → BinarySector) × Bool)) :
    P ⊔ Q = P ∪ Q := by
  rfl

/-- Meet of finite Cantor/Krein sector selections is intersection. -/
@[rep_depth operator]
theorem finiteCantorKreinSectorSet_inf_eq_inter
    {n : Nat} (P Q : Set ((Fin n → BinarySector) × Bool)) :
    P ⊓ Q = P ∩ Q := by
  rfl

/-- Arbitrary join of finite Cantor/Krein sector selections is set union. -/
@[rep_depth operator]
theorem finiteCantorKreinSectorSet_sSup_eq_sUnion
    {n : Nat} (S : Set (Set ((Fin n → BinarySector) × Bool))) :
    sSup S = ⋃₀ S := by
  rfl

/-- Arbitrary meet of finite Cantor/Krein sector selections is set intersection. -/
@[rep_depth operator]
theorem finiteCantorKreinSectorSet_sInf_eq_sInter
    {n : Nat} (S : Set (Set ((Fin n → BinarySector) × Bool))) :
    sInf S = ⋂₀ S := by
  rfl

/-- Indexed join of finite Cantor/Krein sector selections is indexed union. -/
@[rep_depth operator]
theorem finiteCantorKreinSectorSet_iSup_eq_iUnion
    {ι : Sort u} {n : Nat} (S : ι → Set ((Fin n → BinarySector) × Bool)) :
    (⨆ i, S i) = ⋃ i, S i := by
  rfl

/-- Indexed meet of finite Cantor/Krein sector selections is indexed intersection. -/
@[rep_depth operator]
theorem finiteCantorKreinSectorSet_iInf_eq_iInter
    {ι : Sort u} {n : Nat} (S : ι → Set ((Fin n → BinarySector) × Bool)) :
    (⨅ i, S i) = ⋂ i, S i := by
  rfl

/-- Refinement of sector selections along a concrete sector map. -/
@[rep_depth operator]
def sectorRefine {α : Type u} {β : Type v} (f : α → β) (P : Set α) : Set β :=
  f '' P

/-- Coarse-graining of sector selections along a concrete sector map. -/
@[rep_depth operator]
def sectorCoarse {α : Type u} {β : Type v} (f : α → β) (Q : Set β) : Set α :=
  f ⁻¹' Q

/--
Direct image refinement and inverse image coarse-graining form a Galois
connection.  This is the order-theoretic coarse/fine adjunction.
-/
@[rep_depth operator]
theorem sectorRefine_sectorCoarse_galoisConnection
    {α : Type u} {β : Type v} (f : α → β) :
    GaloisConnection (sectorRefine f) (sectorCoarse f) := by
  intro P Q
  exact Set.image_subset_iff

/-- Refinement preserves arbitrary joins, as every lower adjoint does. -/
@[rep_depth operator]
theorem sectorRefine_iSup
    {α : Type u} {β : Type v} {ι : Sort w} (f : α → β) (P : ι → Set α) :
    sectorRefine f (⨆ i, P i) = ⨆ i, sectorRefine f (P i) := by
  exact (sectorRefine_sectorCoarse_galoisConnection f).l_iSup

/-- Coarse-graining preserves arbitrary meets, as every upper adjoint does. -/
@[rep_depth operator]
theorem sectorCoarse_iInf
    {α : Type u} {β : Type v} {ι : Sort w} (f : α → β) (Q : ι → Set β) :
    sectorCoarse f (⨅ i, Q i) = ⨅ i, sectorCoarse f (Q i) := by
  exact (sectorRefine_sectorCoarse_galoisConnection f).u_iInf

/-- Knaster--Tarski: fixed sectors of a monotone map form a complete lattice. -/
@[rep_depth operator]
noncomputable def selfSimilarSectorsCompleteLattice
    {L : Type u} [CompleteLattice L] (R : L →o L) :
    CompleteLattice (Function.fixedPoints R) :=
  fixedPoints.completeLattice R

/-- Membership in the self-similar sector type is exactly the fixed-point equation. -/
@[rep_depth operator]
theorem selfSimilarSector_isFixed
    {L : Type u} [CompleteLattice L] (R : L →o L) (P : Function.fixedPoints R) :
    R P.1 = P.1 :=
  P.2

/-- The least fixed sector supplied by Knaster--Tarski is fixed. -/
@[rep_depth operator]
theorem selfSimilarSector_lfp_isFixed
    {L : Type u} [CompleteLattice L] (R : L →o L) :
    R R.lfp = R.lfp :=
  R.map_lfp

/-- The greatest fixed sector supplied by Knaster--Tarski is fixed. -/
@[rep_depth operator]
theorem selfSimilarSector_gfp_isFixed
    {L : Type u} [CompleteLattice L] (R : L →o L) :
    R R.gfp = R.gfp :=
  R.map_gfp

/-- Arbitrary joins in the Cuntz projection sector powerset are unions. -/
@[rep_depth operator]
theorem CuntzIdempotentSectorSet_iSup_eq_iUnion
    {Op : Type u} [Ring Op] [StarRing Op] {ι : Sort v}
    (S : ι → Set (CuntzO2Carrier.CuntzIdempotent (Op := Op))) :
    (⨆ i, S i) = ⋃ i, S i := by
  rfl

/-- Arbitrary meets in the Cuntz projection sector powerset are intersections. -/
@[rep_depth operator]
theorem CuntzIdempotentSectorSet_iInf_eq_iInter
    {Op : Type u} [Ring Op] [StarRing Op] {ι : Sort v}
    (S : ι → Set (CuntzO2Carrier.CuntzIdempotent (Op := Op))) :
    (⨅ i, S i) = ⋂ i, S i := by
  rfl

end CompleteLatticeSectorCompletion

/-- The self-adjoint Majorana operator obtained from the left Cuntz generator. -/
@[rep_depth operator]
def cuntzMajoranaE1
    {Op : Type*} [Ring Op] [StarRing Op]
    (M : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op) : Op :=
  (CuntzO2Carrier.S_left M) + star (CuntzO2Carrier.S_left M)

/-- The phase-twisted skew part of the left Cuntz generator. -/
@[rep_depth operator]
def cuntzMajoranaE2
    {Op : Type*} [Ring Op] [StarRing Op]
    (phaseAxis : Op) (M : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op) : Op :=
  phaseAxis * ((CuntzO2Carrier.S_left M) - star (CuntzO2Carrier.S_left M))

@[rep_depth operator]
theorem cuntzMajoranaE1_eq
    {Op : Type*} [Ring Op] [StarRing Op]
    (M : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op) :
    cuntzMajoranaE1 M = (CuntzO2Carrier.S_left M) + star (CuntzO2Carrier.S_left M) :=
  rfl

@[rep_depth operator]
theorem cuntzMajoranaE2_eq
    {Op : Type*} [Ring Op] [StarRing Op]
    (phaseAxis : Op) (M : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op) :
    cuntzMajoranaE2 phaseAxis M = phaseAxis * ((CuntzO2Carrier.S_left M) - star (CuntzO2Carrier.S_left M)) :=
  rfl

@[rep_depth operator]
theorem cuntzMajoranaE1_star_eq_self
    {Op : Type*} [Ring Op] [StarRing Op]
    (M : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op) :
    star (cuntzMajoranaE1 M) = cuntzMajoranaE1 M := by
  simp [cuntzMajoranaE1, add_comm]

@[rep_depth operator]
theorem cuntzMajoranaE1_isSelfAdjoint
    {Op : Type*} [Ring Op] [StarRing Op]
    (M : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op) :
    IsSelfAdjoint (cuntzMajoranaE1 M) := by
  simpa [IsSelfAdjoint] using cuntzMajoranaE1_star_eq_self M

@[rep_depth operator]
theorem cuntzMajoranaSkewPart_star_eq_neg
    {Op : Type*} [Ring Op] [StarRing Op]
    (M : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op) :
    star ((CuntzO2Carrier.S_left M) - star (CuntzO2Carrier.S_left M)) = -((CuntzO2Carrier.S_left M) - star (CuntzO2Carrier.S_left M)) := by
  simp [sub_eq_add_neg, add_comm]

@[rep_depth operator]
theorem cuntzMajoranaE2_star_eq_self_of_phaseAxis
    {Op : Type*} [Ring Op] [StarRing Op]
    (phaseAxis : Op) (M : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op)
    (hPhaseStar : star phaseAxis = -phaseAxis)
    (hPhaseComm :
      ((CuntzO2Carrier.S_left M) - star (CuntzO2Carrier.S_left M)) * phaseAxis =
        phaseAxis * ((CuntzO2Carrier.S_left M) - star (CuntzO2Carrier.S_left M))) :
    star (cuntzMajoranaE2 phaseAxis M) = cuntzMajoranaE2 phaseAxis M := by
  unfold cuntzMajoranaE2
  calc
    star (phaseAxis * ((CuntzO2Carrier.S_left M) - star (CuntzO2Carrier.S_left M))) =
        star ((CuntzO2Carrier.S_left M) - star (CuntzO2Carrier.S_left M)) * star phaseAxis := by
      rw [star_mul]
    _ = (-((CuntzO2Carrier.S_left M) - star (CuntzO2Carrier.S_left M))) * (-phaseAxis) := by
      rw [cuntzMajoranaSkewPart_star_eq_neg M, hPhaseStar]
    _ = ((CuntzO2Carrier.S_left M) - star (CuntzO2Carrier.S_left M)) * phaseAxis := by
      noncomm_ring
    _ = phaseAxis * ((CuntzO2Carrier.S_left M) - star (CuntzO2Carrier.S_left M)) := hPhaseComm

@[rep_depth operator]
theorem cuntzMajoranaE2_isSelfAdjoint_of_phaseAxis
    {Op : Type*} [Ring Op] [StarRing Op]
    (phaseAxis : Op) (M : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op)
    (hPhaseStar : star phaseAxis = -phaseAxis)
    (hPhaseComm :
      ((CuntzO2Carrier.S_left M) - star (CuntzO2Carrier.S_left M)) * phaseAxis =
        phaseAxis * ((CuntzO2Carrier.S_left M) - star (CuntzO2Carrier.S_left M))) :
    IsSelfAdjoint (cuntzMajoranaE2 phaseAxis M) := by
  simpa [IsSelfAdjoint] using
    cuntzMajoranaE2_star_eq_self_of_phaseAxis phaseAxis M hPhaseStar hPhaseComm

@[rep_depth operator]
theorem doubledClockAxis_sq_eq_neg_id
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    (clockAxis (E := E)).comp (clockAxis (E := E)) =
      -(ContinuousLinearMap.id ℝ (DoubledSpace E)) := by
  exact InfoGeometry.Canonical.BilingualRealHestenesDictionary.realPhaseAxis_sq (E := E)

@[rep_depth operator]
theorem doubledClockAxis_star_eq_neg
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    star (clockAxis (E := E)) = -(clockAxis (E := E)) := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  apply ContinuousLinearMap.ext
  intro u
  apply ext_inner_left ℝ
  intro v
  rw [ContinuousLinearMap.adjoint_inner_right]
  change
    ⟪clockAxis (E := E) v, u⟫_ℝ =
      ⟪v, -(clockAxis (E := E) u)⟫_ℝ
  rw [inner_neg_right]
  exact InfoGeometry.Canonical.TomitaTakesaki.clockAxis_inner_skew (E := E) v u

@[rep_depth operator]
theorem doubledCuntzMajoranaE2_eq_clockAxis
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (M : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) (Op := DoubledSpace E →L[ℝ] DoubledSpace E)) :
    cuntzMajoranaE2 (clockAxis (E := E)) M =
      clockAxis (E := E) * ((CuntzO2Carrier.S_left M) - star (CuntzO2Carrier.S_left M)) :=
  rfl

@[rep_depth operator]
theorem doubledCuntzMajoranaE2_isSelfAdjoint_of_commutes_clockAxis
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (M : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) (Op := DoubledSpace E →L[ℝ] DoubledSpace E))
    (hComm :
      ((CuntzO2Carrier.S_left M) - star (CuntzO2Carrier.S_left M)) * clockAxis (E := E) =
        clockAxis (E := E) * ((CuntzO2Carrier.S_left M) - star (CuntzO2Carrier.S_left M))) :
    IsSelfAdjoint (cuntzMajoranaE2 (clockAxis (E := E)) M) := by
  exact cuntzMajoranaE2_isSelfAdjoint_of_phaseAxis
    (clockAxis (E := E)) M
    (doubledClockAxis_star_eq_neg (E := E)) hComm

@[rep_depth operator]
theorem doubledCuntzStarLeft_commutes_clockAxis_of_commutes
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (M : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) (Op := DoubledSpace E →L[ℝ] DoubledSpace E))
    (hComm :
      (CuntzO2Carrier.S_left M) * clockAxis (E := E) = clockAxis (E := E) * (CuntzO2Carrier.S_left M)) :
    star (CuntzO2Carrier.S_left M) * clockAxis (E := E) = clockAxis (E := E) * star (CuntzO2Carrier.S_left M) := by
  have hStar :
      star (clockAxis (E := E)) * star (CuntzO2Carrier.S_left M) =
        star (CuntzO2Carrier.S_left M) * star (clockAxis (E := E)) := by
    simpa only [star_mul] using congrArg star hComm
  rw [doubledClockAxis_star_eq_neg (E := E)] at hStar
  have hK :
      clockAxis (E := E) * star (CuntzO2Carrier.S_left M) =
        star (CuntzO2Carrier.S_left M) * clockAxis (E := E) := by
    apply ContinuousLinearMap.ext
    intro x
    have hx := congrArg (fun T : DoubledSpace E →L[ℝ] DoubledSpace E => T x) hStar
    change
      (-(clockAxis (E := E))) (star (CuntzO2Carrier.S_left M) x) =
        star (CuntzO2Carrier.S_left M) ((-(clockAxis (E := E))) x) at hx
    simp only [ContinuousLinearMap.neg_apply, map_neg] at hx
    exact neg_inj.mp hx
  exact hK.symm

@[rep_depth operator]
theorem doubledCuntzSkewLeft_commutes_clockAxis_of_commutes
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (M : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) (Op := DoubledSpace E →L[ℝ] DoubledSpace E))
    (hComm :
      (CuntzO2Carrier.S_left M) * clockAxis (E := E) = clockAxis (E := E) * (CuntzO2Carrier.S_left M)) :
    ((CuntzO2Carrier.S_left M) - star (CuntzO2Carrier.S_left M)) * clockAxis (E := E) =
      clockAxis (E := E) * ((CuntzO2Carrier.S_left M) - star (CuntzO2Carrier.S_left M)) := by
  have hStarComm :
      star (CuntzO2Carrier.S_left M) * clockAxis (E := E) =
        clockAxis (E := E) * star (CuntzO2Carrier.S_left M) :=
    doubledCuntzStarLeft_commutes_clockAxis_of_commutes M hComm
  calc
    ((CuntzO2Carrier.S_left M) - star (CuntzO2Carrier.S_left M)) * clockAxis (E := E) =
        (CuntzO2Carrier.S_left M) * clockAxis (E := E) - star (CuntzO2Carrier.S_left M) * clockAxis (E := E) := by
      rw [sub_mul]
    _ = clockAxis (E := E) * (CuntzO2Carrier.S_left M) -
          clockAxis (E := E) * star (CuntzO2Carrier.S_left M) := by
      rw [hComm, hStarComm]
    _ = clockAxis (E := E) * ((CuntzO2Carrier.S_left M) - star (CuntzO2Carrier.S_left M)) := by
      rw [mul_sub]

@[rep_depth operator]
theorem doubledCuntzE2_isSelfAdjoint_of_commutes_clockAxis
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (M : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) (Op := DoubledSpace E →L[ℝ] DoubledSpace E))
    (hComm :
      (CuntzO2Carrier.S_left M) * clockAxis (E := E) = clockAxis (E := E) * (CuntzO2Carrier.S_left M)) :
    IsSelfAdjoint (cuntzMajoranaE2 (clockAxis (E := E)) M) := by
  exact doubledCuntzMajoranaE2_isSelfAdjoint_of_commutes_clockAxis M
    (doubledCuntzSkewLeft_commutes_clockAxis_of_commutes M hComm)

@[rep_depth operator]
theorem doubledCuntzLeft_commutes_clockAxis_of_KLinear
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (M : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) (Op := DoubledSpace E →L[ℝ] DoubledSpace E))
    (hKLinear :
      InfoGeometry.Canonical.HestenesRealStructures.KLinear (E := E) (CuntzO2Carrier.S_left M)) :
    (CuntzO2Carrier.S_left M) * clockAxis (E := E) = clockAxis (E := E) * (CuntzO2Carrier.S_left M) := by
  change
    (CuntzO2Carrier.S_left M).comp (clockAxis (E := E)) =
      (clockAxis (E := E)).comp (CuntzO2Carrier.S_left M)
  simpa [InfoGeometry.Canonical.HestenesRealStructures.KLinear,
    InfoGeometry.Canonical.BogoliubovTransport.IsPhaseLinear] using hKLinear

@[rep_depth operator]
theorem doubledCuntzE2_isSelfAdjoint_of_KLinear
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (M : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) (Op := DoubledSpace E →L[ℝ] DoubledSpace E))
    (hKLinear :
      InfoGeometry.Canonical.HestenesRealStructures.KLinear (E := E) (CuntzO2Carrier.S_left M)) :
    IsSelfAdjoint (cuntzMajoranaE2 (clockAxis (E := E)) M) := by
  exact doubledCuntzE2_isSelfAdjoint_of_commutes_clockAxis M
    (doubledCuntzLeft_commutes_clockAxis_of_KLinear M hKLinear)

/-- A bounded resolvent packet over a Cuntz/Cantor carrier. -/
@[rep_depth operator]
structure CuntzCantorSpectralTriple
    (Op H : Type*) [Ring Op] [StarRing Op] [NormedAddCommGroup H] [NormedSpace ℂ H]
    [MulAction ℂ H]
    [SMul Op H] where
  cuntz : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op

  /-- Representation of the binary Cantor cylinder algebra in the operator carrier. -/
  cylinderRepresentation : (n : Nat) -> (Fin n → BinarySector) -> Op

  /-- Bounded Dirac datum; unbounded spectral-triple structure is not asserted. -/
  dirac : H →L[ℂ] H

  /-- Representation action used to state bounded commutator data. -/
  representedAction : Op -> H →L[ℂ] H

  spectralParameter : ℂ
  resolvent : H →L[ℂ] H
  resolvent_comp_shift :
    resolvent.comp
        (dirac - spectralParameter • ContinuousLinearMap.id ℂ H) =
      ContinuousLinearMap.id ℂ H
  shift_comp_resolvent :
    (dirac - spectralParameter • ContinuousLinearMap.id ℂ H).comp resolvent =
      ContinuousLinearMap.id ℂ H
  resolvent_compact : IsCompactOperator resolvent

  /-- Spectral dimension readout supplied by the concrete model. -/
  spectralDimension : ℝ


namespace CuntzCantorSpectralTriple

variable {Op H : Type*} [Ring Op] [StarRing Op]
variable [NormedAddCommGroup H] [NormedSpace ℂ H] [MulAction ℂ H] [SMul Op H]
variable (T : CuntzCantorSpectralTriple Op H)

theorem shifted_dirac_injective :
    Function.Injective
      (T.dirac - T.spectralParameter • ContinuousLinearMap.id ℂ H) := by
  intro x y hxy
  have hleft := congrArg (fun U : H →L[ℂ] H => U x) T.resolvent_comp_shift
  have hright := congrArg (fun U : H →L[ℂ] H => U y) T.resolvent_comp_shift
  calc
    x = T.resolvent ((T.dirac - T.spectralParameter •
        ContinuousLinearMap.id ℂ H) x) := by simpa using hleft.symm
    _ = T.resolvent ((T.dirac - T.spectralParameter •
        ContinuousLinearMap.id ℂ H) y) := by rw [hxy]
    _ = y := by simpa using hright

theorem shifted_dirac_surjective :
    Function.Surjective
      (T.dirac - T.spectralParameter • ContinuousLinearMap.id ℂ H) := by
  intro y
  refine ⟨T.resolvent y, ?_⟩
  have hright := congrArg (fun U : H →L[ℂ] H => U y) T.shift_comp_resolvent
  simpa using hright

theorem shifted_dirac_bijective :
    Function.Bijective
      (T.dirac - T.spectralParameter • ContinuousLinearMap.id ℂ H) :=
  ⟨T.shifted_dirac_injective, T.shifted_dirac_surjective⟩

theorem resolvent_apply_shifted_dirac (x : H) :
    T.resolvent
        ((T.dirac - T.spectralParameter • ContinuousLinearMap.id ℂ H) x) = x := by
  have h := congrArg (fun U : H →L[ℂ] H => U x) T.resolvent_comp_shift
  simpa using h

theorem shifted_dirac_apply_resolvent (x : H) :
    (T.dirac - T.spectralParameter • ContinuousLinearMap.id ℂ H)
        (T.resolvent x) = x := by
  have h := congrArg (fun U : H →L[ℂ] H => U x) T.shift_comp_resolvent
  simpa using h

theorem shifted_dirac_resolvent_commutes :
    (T.dirac - T.spectralParameter • ContinuousLinearMap.id ℂ H).comp
        T.resolvent =
      T.resolvent.comp
        (T.dirac - T.spectralParameter • ContinuousLinearMap.id ℂ H) := by
  rw [T.shift_comp_resolvent, T.resolvent_comp_shift]

theorem shifted_dirac_resolvent_unique_right
    (R : H →L[ℂ] H)
    (hright :
      (T.dirac - T.spectralParameter • ContinuousLinearMap.id ℂ H).comp R =
        ContinuousLinearMap.id ℂ H) :
    R = T.resolvent := by
  calc
    R = (ContinuousLinearMap.id ℂ H).comp R := by simp
    _ = (T.resolvent.comp
        (T.dirac - T.spectralParameter • ContinuousLinearMap.id ℂ H)).comp R := by
      rw [T.resolvent_comp_shift]
    _ = T.resolvent.comp
        ((T.dirac - T.spectralParameter • ContinuousLinearMap.id ℂ H).comp R) := by
      rfl
    _ = T.resolvent.comp (ContinuousLinearMap.id ℂ H) := by rw [hright]
    _ = T.resolvent := by simp

theorem shifted_dirac_resolvent_unique
    (R : H →L[ℂ] H)
    (hleft : R.comp
        (T.dirac - T.spectralParameter • ContinuousLinearMap.id ℂ H) =
      ContinuousLinearMap.id ℂ H) :
    R = T.resolvent := by
  calc
    R = R.comp (ContinuousLinearMap.id ℂ H) := by simp
    _ = R.comp ((T.dirac - T.spectralParameter •
        ContinuousLinearMap.id ℂ H).comp T.resolvent) := by
      rw [T.shift_comp_resolvent]
    _ = (R.comp (T.dirac - T.spectralParameter •
        ContinuousLinearMap.id ℂ H)).comp T.resolvent := by
      rfl
    _ = (ContinuousLinearMap.id ℂ H).comp T.resolvent := by
      rw [hleft]
    _ = T.resolvent := by simp

theorem resolvent_bijective :
    Function.Bijective T.resolvent := by
  constructor
  · intro x y hxy
    calc
      x = (T.dirac - T.spectralParameter • ContinuousLinearMap.id ℂ H)
          (T.resolvent x) :=
        (T.shifted_dirac_apply_resolvent x).symm
      _ = (T.dirac - T.spectralParameter • ContinuousLinearMap.id ℂ H)
          (T.resolvent y) := by
        exact congrArg
          (fun z : H =>
            (T.dirac - T.spectralParameter • ContinuousLinearMap.id ℂ H) z)
          hxy
      _ = y := T.shifted_dirac_apply_resolvent y
  · intro y
    refine ⟨(T.dirac - T.spectralParameter • ContinuousLinearMap.id ℂ H) y, ?_⟩
    exact T.resolvent_apply_shifted_dirac y

theorem finiteDimensional_of_compact_resolvent
    (T : CuntzCantorSpectralTriple Op H) :
    FiniteDimensional ℂ H := by
  let A : H →L[ℂ] H :=
    T.dirac - T.spectralParameter • ContinuousLinearMap.id ℂ H
  have hcompact_comp : IsCompactOperator (A.comp T.resolvent) := by
    simpa [Function.comp_def, ContinuousLinearMap.comp_apply, A] using
      T.resolvent_compact.clm_comp A
  have hcompact_id : IsCompactOperator (ContinuousLinearMap.id ℂ H) := by
    rw [← T.shift_comp_resolvent]
    exact hcompact_comp
  rcases hcompact_id.image_closedBall_subset_compact 1 with ⟨K, hK, hsub⟩
  have hball : IsCompact (Metric.closedBall (0 : H) 1) :=
    hK.of_isClosed_subset Metric.isClosed_closedBall (by
      intro x hx
      exact hsub ⟨x, hx, rfl⟩)
  exact FiniteDimensional.of_isCompact_closedBall₀ ℂ zero_lt_one hball

theorem no_infiniteDimensional_cuntzCantorSpectralTriple
    (T : CuntzCantorSpectralTriple Op H)
    (hH : ¬ FiniteDimensional ℂ H) : False := by
  exact hH (finiteDimensional_of_compact_resolvent T)

/-- The left Cuntz range projection of the spectral-triple carrier. -/
@[rep_depth operator]
def leftCylinderProjection : Op :=
  CuntzO2Carrier.leftRangeProjection T.cuntz

/-- The right Cuntz range projection of the spectral-triple carrier. -/
@[rep_depth operator]
def rightCylinderProjection : Op :=
  CuntzO2Carrier.rightRangeProjection T.cuntz

/-- Cylinder projections cover the binary boundary at the first level. -/
@[rep_depth operator]
theorem firstLevelCylinder_sum_one :
    leftCylinderProjection T + rightCylinderProjection T = 1 := by
  exact CuntzO2Carrier.rangeProjection_sum_one T.cuntz

theorem leftCylinderProjection_idempotent :
    leftCylinderProjection T * leftCylinderProjection T =
      leftCylinderProjection T := by
  unfold leftCylinderProjection CuntzO2Carrier.leftRangeProjection
  calc
    (CuntzO2Carrier.S_left T.cuntz * star (CuntzO2Carrier.S_left T.cuntz)) *
        (CuntzO2Carrier.S_left T.cuntz * star (CuntzO2Carrier.S_left T.cuntz)) =
      CuntzO2Carrier.S_left T.cuntz *
        (star (CuntzO2Carrier.S_left T.cuntz) *
          CuntzO2Carrier.S_left T.cuntz) *
        star (CuntzO2Carrier.S_left T.cuntz) := by
          noncomm_ring
    _ = CuntzO2Carrier.S_left T.cuntz * 1 *
        star (CuntzO2Carrier.S_left T.cuntz) := by
          rw [CuntzO2Carrier.left_isometry T.cuntz]
    _ = leftCylinderProjection T := by
          simp [leftCylinderProjection, CuntzO2Carrier.leftRangeProjection]

theorem rightCylinderProjection_idempotent :
    rightCylinderProjection T * rightCylinderProjection T =
      rightCylinderProjection T := by
  unfold rightCylinderProjection CuntzO2Carrier.rightRangeProjection
  calc
    (CuntzO2Carrier.S_right T.cuntz * star (CuntzO2Carrier.S_right T.cuntz)) *
        (CuntzO2Carrier.S_right T.cuntz * star (CuntzO2Carrier.S_right T.cuntz)) =
      CuntzO2Carrier.S_right T.cuntz *
        (star (CuntzO2Carrier.S_right T.cuntz) *
          CuntzO2Carrier.S_right T.cuntz) *
        star (CuntzO2Carrier.S_right T.cuntz) := by
          noncomm_ring
    _ = CuntzO2Carrier.S_right T.cuntz * 1 *
        star (CuntzO2Carrier.S_right T.cuntz) := by
          rw [CuntzO2Carrier.right_isometry T.cuntz]
    _ = rightCylinderProjection T := by
          simp [rightCylinderProjection, CuntzO2Carrier.rightRangeProjection]

theorem leftCylinderProjection_star :
    star (leftCylinderProjection T) = leftCylinderProjection T := by
  exact CuntzO2Carrier.leftRangeProjection_star T.cuntz

theorem rightCylinderProjection_star :
    star (rightCylinderProjection T) = rightCylinderProjection T := by
  exact CuntzO2Carrier.rightRangeProjection_star T.cuntz

theorem leftCylinderProjection_isStarProjection :
    IsStarProjection (leftCylinderProjection T) := by
  rw [isStarProjection_iff]
  exact ⟨leftCylinderProjection_idempotent T,
    leftCylinderProjection_star T⟩

theorem rightCylinderProjection_isStarProjection :
    IsStarProjection (rightCylinderProjection T) := by
  rw [isStarProjection_iff]
  exact ⟨rightCylinderProjection_idempotent T,
    rightCylinderProjection_star T⟩

theorem leftCylinderProjection_mul_rightCylinderProjection :
    leftCylinderProjection T * rightCylinderProjection T = 0 := by
  unfold leftCylinderProjection rightCylinderProjection
    CuntzO2Carrier.leftRangeProjection CuntzO2Carrier.rightRangeProjection
  calc
    (CuntzO2Carrier.S_left T.cuntz * star (CuntzO2Carrier.S_left T.cuntz)) *
        (CuntzO2Carrier.S_right T.cuntz * star (CuntzO2Carrier.S_right T.cuntz)) =
      CuntzO2Carrier.S_left T.cuntz *
        (star (CuntzO2Carrier.S_left T.cuntz) *
          CuntzO2Carrier.S_right T.cuntz) *
        star (CuntzO2Carrier.S_right T.cuntz) := by
          noncomm_ring
    _ = 0 := by
      rw [CuntzO2Carrier.orthogonal_ranges T.cuntz |>.1]
      simp

theorem rightCylinderProjection_mul_leftCylinderProjection :
    rightCylinderProjection T * leftCylinderProjection T = 0 := by
  unfold rightCylinderProjection leftCylinderProjection
    CuntzO2Carrier.rightRangeProjection CuntzO2Carrier.leftRangeProjection
  calc
    (CuntzO2Carrier.S_right T.cuntz * star (CuntzO2Carrier.S_right T.cuntz)) *
        (CuntzO2Carrier.S_left T.cuntz * star (CuntzO2Carrier.S_left T.cuntz)) =
      CuntzO2Carrier.S_right T.cuntz *
        (star (CuntzO2Carrier.S_right T.cuntz) *
          CuntzO2Carrier.S_left T.cuntz) *
        star (CuntzO2Carrier.S_left T.cuntz) := by
          noncomm_ring
    _ = 0 := by
      rw [CuntzO2Carrier.orthogonal_ranges T.cuntz |>.2]
      simp

/-- The installed resolvent representative is compact. -/
@[rep_depth operator]
theorem compactResolventOrSummability_holds :
    IsCompactOperator T.resolvent :=
  T.resolvent_compact

end CuntzCantorSpectralTriple

end InfoGeometry.Topology
