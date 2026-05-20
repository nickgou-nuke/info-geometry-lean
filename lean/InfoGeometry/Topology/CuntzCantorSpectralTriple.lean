import Mathlib
import InfoGeometry.OperatorAlgebra.ErlangenNet
import InfoGeometry.OperatorAlgebra.SpectralTriple
import InfoGeometry.Canonical.BilingualRealHestenesDictionary
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

noncomputable section

namespace InfoGeometry.Topology

open InfoGeometry.Krein

/-!
# Cuntz/Cantor spectral triple socket

This file gives a theorem-safe analytic socket for turning the symbolic binary
boundary of `ErlangenNet` into an operator-algebraic carrier.

The module deliberately separates four layers:

* a binary symbolic boundary `N -> BinarySector`;
* Cuntz `O_2`-style isometry data on an abstract star algebra;
* candidate Majorana/Clifford operators built from shifts;
* a witness-gated Cantor spectral-triple packet.

Guardrail: the Cuntz relations alone do not prove that `S + S*` is a Clifford
unitary. The CAR/Clifford laws are therefore carried by explicit witnesses.
Likewise, the Dirac operator and Hausdorff-dimension readout are supplied as
spectral-triple data, not derived from the Cuntz carrier alone.
-/

open InfoGeometry.OperatorAlgebra.ErlangenNet

/-- Binary Cantor boundary used by the operator-Erlangen net. -/
abbrev BinaryCantorBoundary := SectorBoundary BinarySector

/-- Finite binary cylinder word of depth `n`. -/
abbrev BinaryCylinder (n : Nat) := FiniteSectorWord BinarySector n

/-- Prefixing a binary symbol to an infinite Cantor code. -/
@[rep_depth operator]
def prefixBoundary (s : BinarySector) (x : BinaryCantorBoundary) : BinaryCantorBoundary
    | 0 => s
    | n + 1 => x n

@[rep_depth operator]
theorem prefixBoundary_zero
    (s : BinarySector) (x : BinaryCantorBoundary) :
    prefixBoundary s x 0 = s :=
  rfl

@[rep_depth operator]
theorem prefixBoundary_succ
    (s : BinarySector) (x : BinaryCantorBoundary) (n : Nat) :
    prefixBoundary s x (n + 1) = x n :=
  rfl

/-- Abstract Cuntz `O_2` carrier in a star ring. -/
@[rep_depth operator]
structure CuntzO2Carrier
    (Op : Type*) [Ring Op] [StarRing Op] where
  S_left : Op
  S_right : Op

  left_isometry :
    star S_left * S_left = 1

  right_isometry :
    star S_right * S_right = 1

  orthogonal_ranges :
    star S_left * S_right = 0 ∧ star S_right * S_left = 0

  range_sum :
    S_left * star S_left + S_right * star S_right = 1

namespace CuntzO2Carrier

variable {Op : Type*} [Ring Op] [StarRing Op]
variable (C : CuntzO2Carrier Op)

/-- Left range projection `S_1 S_1*`. -/
@[rep_depth operator]
def leftRangeProjection : Op :=
  C.S_left * star C.S_left

/-- Right range projection `S_2 S_2*`. -/
@[rep_depth operator]
def rightRangeProjection : Op :=
  C.S_right * star C.S_right

/-- The two range projections sum to the identity by the Cuntz relation. -/
@[rep_depth operator]
theorem rangeProjection_sum_one :
    C.leftRangeProjection + C.rightRangeProjection = 1 := by
  exact C.range_sum

/--
Projection subequivalence on the current Cuntz carrier.

This is the smallest order-theoretic relation we can state without building a
full Cuntz semigroup quotient.
-/
@[rep_depth operator]
def projectionSubequiv (p q : Op) : Prop :=
  p * q = p

/-- A projection is subequivalent to itself when it is idempotent. -/
@[rep_depth operator]
theorem projectionSubequiv_refl
    (p : Op) (hp : p * p = p) :
    projectionSubequiv p p := by
  exact hp

/-- Transitivity of projection subequivalence. -/
@[rep_depth operator]
theorem projectionSubequiv_trans
    {p q r : Op}
    (hpq : projectionSubequiv p q)
    (hqr : projectionSubequiv q r) :
    projectionSubequiv p r := by
  calc
    p * r = (p * q) * r := by
      rw [hpq]
    _ = p * (q * r) := by
      rw [mul_assoc]
    _ = p * q := by
      rw [hqr]
    _ = p := by
      rw [hpq]

/-- The left Cuntz range projection is subequivalent to the unit. -/
@[rep_depth operator]
theorem leftRangeProjection_subequiv_one :
    projectionSubequiv C.leftRangeProjection 1 := by
  simpa [projectionSubequiv, C.rangeProjection_sum_one] using
    C.leftRangeProjection_absorb_sum_one

/-- The right Cuntz range projection is subequivalent to the unit. -/
@[rep_depth operator]
theorem rightRangeProjection_subequiv_one :
    projectionSubequiv C.rightRangeProjection 1 := by
  simpa [projectionSubequiv, C.rangeProjection_sum_one] using
    C.rightRangeProjection_absorb_sum_one

/-- The left range projection is subequivalent to itself. -/
@[rep_depth operator]
theorem leftRangeProjection_subequiv_self :
    projectionSubequiv C.leftRangeProjection C.leftRangeProjection := by
  unfold projectionSubequiv leftRangeProjection
  calc
    (C.S_left * star C.S_left) * (C.S_left * star C.S_left)
        = C.S_left * (star C.S_left * C.S_left) * star C.S_left := by
            noncomm_ring
    _ = C.S_left * 1 * star C.S_left := by
          rw [C.left_isometry]
    _ = C.S_left * star C.S_left := by
          simp

/-- The right range projection is subequivalent to itself. -/
@[rep_depth operator]
theorem rightRangeProjection_subequiv_self :
    projectionSubequiv C.rightRangeProjection C.rightRangeProjection := by
  unfold projectionSubequiv rightRangeProjection
  calc
    (C.S_right * star C.S_right) * (C.S_right * star C.S_right)
        = C.S_right * (star C.S_right * C.S_right) * star C.S_right := by
            noncomm_ring
    _ = C.S_right * 1 * star C.S_right := by
          rw [C.right_isometry]
    _ = C.S_right * star C.S_right := by
          simp

/--
Absorption of the left range projection by the Cuntz partition of unity.

This is the first order-theoretic readout for the Cuntz carrier.
-/
@[rep_depth operator]
theorem leftRangeProjection_absorb_sum_one :
    C.leftRangeProjection * (C.leftRangeProjection + C.rightRangeProjection)
      = C.leftRangeProjection := by
  calc
    C.leftRangeProjection * (C.leftRangeProjection + C.rightRangeProjection)
        = C.leftRangeProjection * 1 := by
            rw [C.rangeProjection_sum_one]
    _ = C.leftRangeProjection := by
          rw [mul_one]

/--
Absorption of the right range projection by the Cuntz partition of unity.

This is the symmetric order-theoretic readout for the Cuntz carrier.
-/
@[rep_depth operator]
theorem rightRangeProjection_absorb_sum_one :
    C.rightRangeProjection * (C.leftRangeProjection + C.rightRangeProjection)
      = C.rightRangeProjection := by
  calc
    C.rightRangeProjection * (C.leftRangeProjection + C.rightRangeProjection)
        = C.rightRangeProjection * 1 := by
            rw [C.rangeProjection_sum_one]
    _ = C.rightRangeProjection := by
          rw [mul_one]

/--
First-level Cuntz decomposition on the operator carrier.

Any element splits into its left and right branch components under the Cuntz
range projections.
-/
@[rep_depth operator]
theorem rangeProjection_decomposition (x : Op) :
    C.leftRangeProjection * x + C.rightRangeProjection * x = x := by
  calc
    C.leftRangeProjection * x + C.rightRangeProjection * x
        = (C.leftRangeProjection + C.rightRangeProjection) * x := by
            rw [add_mul]
    _ = x := by
          rw [C.rangeProjection_sum_one, one_mul]

/--
Right-first decomposition of the operator carrier by the Cuntz range
projections.
-/
@[rep_depth operator]
theorem rangeProjection_decomposition_right (x : Op) :
    x * C.leftRangeProjection + x * C.rightRangeProjection = x := by
  calc
    x * C.leftRangeProjection + x * C.rightRangeProjection
        = x * (C.leftRangeProjection + C.rightRangeProjection) := by
            rw [mul_add]
    _ = x := by
          rw [C.rangeProjection_sum_one, mul_one]

/-- Left range projection is idempotent. -/
@[rep_depth operator]
theorem leftRangeProjection_idempotent :
    C.leftRangeProjection * C.leftRangeProjection = C.leftRangeProjection := by
  unfold leftRangeProjection
  calc
    (C.S_left * star C.S_left) * (C.S_left * star C.S_left)
        = C.S_left * (star C.S_left * C.S_left) * star C.S_left := by
          noncomm_ring
    _ = C.S_left * 1 * star C.S_left := by
          rw [C.left_isometry]
    _ = C.S_left * star C.S_left := by
          simp

/-- Right range projection is idempotent. -/
@[rep_depth operator]
theorem rightRangeProjection_idempotent :
    C.rightRangeProjection * C.rightRangeProjection = C.rightRangeProjection := by
  unfold rightRangeProjection
  calc
    (C.S_right * star C.S_right) * (C.S_right * star C.S_right)
        = C.S_right * (star C.S_right * C.S_right) * star C.S_right := by
          noncomm_ring
    _ = C.S_right * 1 * star C.S_right := by
          rw [C.right_isometry]
    _ = C.S_right * star C.S_right := by
          simp

/--
Idempotent elements of the Cuntz carrier, packaged as a concrete subtype.

This is the first honest carrier for a Cuntz-style projection theory.
-/
@[rep_depth operator]
def CuntzProjection := { p : Op // p * p = p }

namespace CuntzProjection

variable {Op : Type*} [Ring Op] [StarRing Op]

/-- A Cuntz projection remembers its underlying operator. -/
@[rep_depth operator]
def val (p : CuntzProjection (Op := Op)) : Op := p.1

/-- The idempotence proof of a Cuntz projection. -/
@[rep_depth operator]
theorem isIdempotent (p : CuntzProjection (Op := Op)) :
    p.val * p.val = p.val := p.2

end CuntzProjection

/-- Lift a Cuntz carrier range projection to the projection subtype. -/
@[rep_depth operator]
def leftCuntzProjection :
    CuntzProjection (Op := Op) where
  val := C.leftRangeProjection
  property := C.leftRangeProjection_idempotent

/-- Lift the right Cuntz range projection to the projection subtype. -/
@[rep_depth operator]
def rightCuntzProjection :
    CuntzProjection (Op := Op) where
  val := C.rightRangeProjection
  property := C.rightRangeProjection_idempotent

/--
Subequivalence between Cuntz projections.

This is the relation we can safely use as the seed of a Cuntz-style semigroup
development.
-/
@[rep_depth operator]
def projectionPreorder (p q : CuntzProjection (Op := Op)) : Prop :=
  projectionSubequiv p.val q.val

/-- Reflexivity of the projection preorder. -/
@[rep_depth operator]
theorem projectionPreorder_refl (p : CuntzProjection (Op := Op)) :
    projectionPreorder p p := by
  exact projectionSubequiv_refl p.val p.2

/-- Transitivity of the projection preorder. -/
@[rep_depth operator]
theorem projectionPreorder_trans
    {p q r : CuntzProjection (Op := Op)}
    (hpq : projectionPreorder p q)
    (hqr : projectionPreorder q r) :
    projectionPreorder p r := by
  exact projectionSubequiv_trans hpq hqr

/-- The projection preorder is the native preorder on Cuntz projections. -/
@[rep_depth operator]
instance instLE : LE (CuntzProjection (Op := Op)) where
  le p q := projectionPreorder p q

/-- The projection preorder is reflexive and transitive. -/
@[rep_depth operator]
instance instPreorder : Preorder (CuntzProjection (Op := Op)) where
  le_refl := projectionPreorder_refl
  le_trans := by
    intro a b c hab hbc
    exact projectionPreorder_trans (p := a) (q := b) (r := c) hab hbc

/-- The unit element as a Cuntz projection. -/
@[rep_depth operator]
def unitCuntzProjection : CuntzProjection (Op := Op) where
  val := 1
  property := by
    simp

/-- The zero element as a Cuntz projection. -/
@[rep_depth operator]
def zeroCuntzProjection : CuntzProjection (Op := Op) where
  val := 0
  property := by
    simp

/--
Orthogonality of Cuntz projections.

This is the compatibility hypothesis needed to form an additive projection sum.
-/
@[rep_depth operator]
def projectionOrthogonal (p q : CuntzProjection (Op := Op)) : Prop :=
  p.val * q.val = 0 ∧ q.val * p.val = 0

/-- Zero is orthogonal to every Cuntz projection on the left. -/
@[rep_depth operator]
theorem zeroProjectionOrthogonal_left (p : CuntzProjection (Op := Op)) :
    projectionOrthogonal (zeroCuntzProjection (Op := Op)) p := by
  constructor
  · change (0 : Op) * p.val = 0
    simp
  · change p.val * (0 : Op) = 0
    simp

/-- Zero is orthogonal to every Cuntz projection on the right. -/
@[rep_depth operator]
theorem zeroProjectionOrthogonal_right (p : CuntzProjection (Op := Op)) :
    projectionOrthogonal p (zeroCuntzProjection (Op := Op)) := by
  constructor
  · change p.val * (0 : Op) = 0
    simp
  · change (0 : Op) * p.val = 0
    simp

/--
Orthogonal sum of Cuntz projections.

This is the first theorem-backed additive operation on the projection carrier.
-/
@[rep_depth operator]
def orthogonalSum
    (p q : CuntzProjection (Op := Op))
    (h : projectionOrthogonal p q) : CuntzProjection (Op := Op) where
  val := p.val + q.val
  property := by
    unfold projectionOrthogonal at h
    have hpq : p.val * q.val = 0 := h.1
    have hqp : q.val * p.val = 0 := h.2
    calc
      (p.val + q.val) * (p.val + q.val)
          = p.val * p.val + p.val * q.val + q.val * p.val + q.val * q.val := by
              noncomm_ring
      _ = p.val * p.val + q.val * q.val := by simp [hpq, hqp]
      _ = p.val + q.val := by
            have hp : p.val * p.val = p.val := p.2
            have hq : q.val * q.val = q.val := q.2
            simpa [hp, hq]

/-- Orthogonal sum is commutative when the orthogonality data is swapped. -/
@[rep_depth operator]
theorem orthogonalSum_comm
    (p q : CuntzProjection (Op := Op))
    (h : projectionOrthogonal p q) :
    orthogonalSum p q h = orthogonalSum q p ⟨h.2, h.1⟩ := by
  apply Subtype.ext
  change p.val + q.val = q.val + p.val
  simpa [add_comm]

/-- Orthogonal sum with zero on the left is the original projection. -/
@[rep_depth operator]
theorem orthogonalSum_zero_left
    (p : CuntzProjection (Op := Op)) :
    orthogonalSum (zeroCuntzProjection (Op := Op)) p
      (zeroProjectionOrthogonal_left (p := p)) = p := by
  apply Subtype.ext
  change (0 : Op) + p.val = p.val
  simp

/-- Orthogonal sum with zero on the right is the original projection. -/
@[rep_depth operator]
theorem orthogonalSum_zero_right
    (p : CuntzProjection (Op := Op)) :
    orthogonalSum p (zeroCuntzProjection (Op := Op))
      (zeroProjectionOrthogonal_right (p := p)) = p := by
  apply Subtype.ext
  change p.val + (0 : Op) = p.val
  simp

/-- The sum of an orthogonal pair is orthogonal to a third projection if each summand is. -/
@[rep_depth operator]
theorem orthogonalSum_right_orthogonal
    (p q r : CuntzProjection (Op := Op))
    (hpq : projectionOrthogonal p q)
    (hpr : projectionOrthogonal p r)
    (hqr : projectionOrthogonal q r) :
    projectionOrthogonal (orthogonalSum p q hpq) r := by
  constructor
  · change (p.val + q.val) * r.val = 0
    calc
      (p.val + q.val) * r.val = p.val * r.val + q.val * r.val := by
        rw [add_mul]
      _ = 0 := by
        rw [hpr.1, hqr.1]
        simp
  · change r.val * (p.val + q.val) = 0
    calc
      r.val * (p.val + q.val) = r.val * p.val + r.val * q.val := by
        rw [mul_add]
      _ = 0 := by
        rw [hpr.2, hqr.2]
        simp

/-- The sum of a third projection with an orthogonal pair is orthogonal if each summand is. -/
@[rep_depth operator]
theorem orthogonalSum_left_orthogonal
    (p q r : CuntzProjection (Op := Op))
    (hpq : projectionOrthogonal p q)
    (hpr : projectionOrthogonal p r)
    (hqr : projectionOrthogonal q r) :
    projectionOrthogonal p (orthogonalSum q r hqr) := by
  constructor
  · change p.val * (q.val + r.val) = 0
    calc
      p.val * (q.val + r.val) = p.val * q.val + p.val * r.val := by
        rw [mul_add]
      _ = 0 := by
        rw [hpq.1, hpr.1]
        simp
  · change (q.val + r.val) * p.val = 0
    calc
      (q.val + r.val) * p.val = q.val * p.val + r.val * p.val := by
        rw [add_mul]
      _ = 0 := by
        rw [hpq.2, hpr.2]
        simp

/-- Orthogonal sum is associative on pairwise orthogonal triples. -/
@[rep_depth operator]
theorem orthogonalSum_assoc
    (p q r : CuntzProjection (Op := Op))
    (hpq : projectionOrthogonal p q)
    (hpr : projectionOrthogonal p r)
    (hqr : projectionOrthogonal q r) :
    orthogonalSum (orthogonalSum p q hpq) r (orthogonalSum_right_orthogonal p q r hpq hpr hqr) =
      orthogonalSum p (orthogonalSum q r hqr) (orthogonalSum_left_orthogonal p q r hpq hpr hqr) := by
  apply Subtype.ext
  change (p.val + q.val) + r.val = p.val + (q.val + r.val)
  abel

/- The left and right range projections are orthogonal on the left product. -/
@[rep_depth operator]
theorem leftRangeProjection_mul_rightRangeProjection_eq_zero :
    C.leftRangeProjection * C.rightRangeProjection = 0 := by
  unfold leftRangeProjection rightRangeProjection
  calc
    (C.S_left * star C.S_left) * (C.S_right * star C.S_right)
        = C.S_left * (star C.S_left * C.S_right) * star C.S_right := by
          noncomm_ring
    _ = C.S_left * 0 * star C.S_right := by
          rw [C.orthogonal_ranges.1]
    _ = 0 := by
          simp

/-- The left and right range projections are orthogonal on the right product. -/
@[rep_depth operator]
theorem rightRangeProjection_mul_leftRangeProjection_eq_zero :
    C.rightRangeProjection * C.leftRangeProjection = 0 := by
  unfold leftRangeProjection rightRangeProjection
  calc
    (C.S_right * star C.S_right) * (C.S_left * star C.S_left)
        = C.S_right * (star C.S_right * C.S_left) * star C.S_left := by
          noncomm_ring
    _ = C.S_right * 0 * star C.S_left := by
          rw [C.orthogonal_ranges.2]
    _ = 0 := by
          simp

/-- The left and right Cuntz projections are orthogonal. -/
@[rep_depth operator]
theorem leftRightCuntzProjection_orthogonal :
    projectionOrthogonal (leftCuntzProjection (C := C)) (rightCuntzProjection (C := C)) := by
  constructor
  · exact leftRangeProjection_mul_rightRangeProjection_eq_zero (C := C)
  · exact rightRangeProjection_mul_leftRangeProjection_eq_zero (C := C)

/-- The left and right Cuntz projections sum orthogonally to the unit. -/
@[rep_depth operator]
theorem leftRightOrthogonalSum_eq_unit :
    orthogonalSum (leftCuntzProjection (C := C)) (rightCuntzProjection (C := C))
      (leftRightCuntzProjection_orthogonal (C := C)) = unitCuntzProjection (Op := Op) := by
  apply Subtype.ext
  change C.leftRangeProjection + C.rightRangeProjection = 1
  simpa [leftCuntzProjection, rightCuntzProjection, unitCuntzProjection] using
    C.rangeProjection_sum_one

/-- The left summand lies below its orthogonal sum. -/
@[rep_depth operator]
theorem left_le_orthogonalSum
    (p q : CuntzProjection (Op := Op))
    (h : projectionOrthogonal p q) :
    p ≤ orthogonalSum p q h := by
  change p.val * (p.val + q.val) = p.val
  have hp : p.val * p.val = p.val := p.2
  have hq : p.val * q.val = 0 := h.1
  calc
    p.val * (p.val + q.val) = p.val * p.val + p.val * q.val := by
      rw [mul_add]
    _ = p.val := by
      rw [hp, hq]
      simp

/-- The right summand lies below its orthogonal sum. -/
@[rep_depth operator]
theorem right_le_orthogonalSum
    (p q : CuntzProjection (Op := Op))
    (h : projectionOrthogonal p q) :
    q ≤ orthogonalSum p q h := by
  change q.val * (p.val + q.val) = q.val
  have hq : q.val * q.val = q.val := q.2
  have hpq : q.val * p.val = 0 := h.2
  calc
    q.val * (p.val + q.val) = q.val * p.val + q.val * q.val := by
      rw [mul_add]
    _ = q.val := by
      rw [hpq, hq]
      simp

/-- The left range projection lies below the unit in the projection preorder. -/
@[rep_depth operator]
theorem leftRangeProjection_le_unit :
    leftCuntzProjection (C := C) ≤ unitCuntzProjection (Op := Op) := by
  exact leftRangeProjection_subequiv_one (C := C)

/-- The right range projection lies below the unit in the projection preorder. -/
@[rep_depth operator]
theorem rightRangeProjection_le_unit :
    rightCuntzProjection (C := C) ≤ unitCuntzProjection (Op := Op) := by
  exact rightRangeProjection_subequiv_one (C := C)

/--
Projection equivalence on the Cuntz carrier.

This is the mutual subequivalence relation used as the next Cuntz-style
quotient candidate.
-/
@[rep_depth operator]
def projectionEquivalent (p q : Op) : Prop :=
  projectionSubequiv p q ∧ projectionSubequiv q p

/-- Reflexivity of projection equivalence on a projection. -/
@[rep_depth operator]
theorem projectionEquivalent_refl
    (p : Op) (hp : p * p = p) :
    projectionEquivalent p p := by
  constructor
  · exact projectionSubequiv_refl p hp
  · exact projectionSubequiv_refl p hp

/-- Symmetry of projection equivalence. -/
@[rep_depth operator]
theorem projectionEquivalent_symm
    {p q : Op}
    (hpq : projectionEquivalent p q) :
    projectionEquivalent q p := by
  constructor
  · exact hpq.2
  · exact hpq.1

/-- Transitivity of projection equivalence. -/
@[rep_depth operator]
theorem projectionEquivalent_trans
    {p q r : Op}
    (hpq : projectionEquivalent p q)
    (hqr : projectionEquivalent q r) :
    projectionEquivalent p r := by
  constructor
  · exact projectionSubequiv_trans hpq.1 hqr.1
  · exact projectionSubequiv_trans hqr.2 hpq.2

/-- The orthogonal sum does not depend on the chosen orthogonality proof. -/
@[rep_depth operator]
theorem orthogonalSum_proof_irrel
    (p q : CuntzProjection (Op := Op))
    (h h' : projectionOrthogonal p q) :
    orthogonalSum p q h = orthogonalSum p q h' := by
  apply Subtype.ext
  rfl

/--
Setoid of Cuntz projections under projection equivalence.

This is the honest quotient relation for the current projection carrier.
-/
@[rep_depth operator]
def CuntzProjectionSetoid : Setoid (CuntzProjection (Op := Op)) where
  r p q := projectionEquivalent p.val q.val
  iseqv := by
    constructor
    · intro p
      exact projectionEquivalent_refl p.val p.2
    · intro p q h
      exact projectionEquivalent_symm h
    · intro p q r hpq hqr
      exact projectionEquivalent_trans hpq hqr

/-- The Cuntz quotient carrier generated by the projection setoid. -/
@[rep_depth operator]
abbrev CuntzCu := Quotient (CuntzProjectionSetoid (Op := Op))

/-- The quotient class of an orthogonal sum is independent of the orthogonality witness. -/
@[rep_depth operator]
theorem CuntzCu_orthogonalSum_proof_irrel
    (p q : CuntzProjection (Op := Op))
    (h h' : projectionOrthogonal p q) :
    (Quotient.mk (CuntzProjectionSetoid (Op := Op)) (orthogonalSum p q h) : CuntzCu) =
      Quotient.mk (CuntzProjectionSetoid (Op := Op)) (orthogonalSum p q h') := by
  refine Quotient.sound ?_
  simpa [orthogonalSum_proof_irrel p q h h'] using
    (projectionEquivalent_refl (orthogonalSum p q h).val (orthogonalSum p q h).property)

/--
The projection preorder is invariant under projection equivalence on both sides.
This is the key descent lemma for the quotient carrier.
-/
@[rep_depth operator]
theorem projectionPreorder_congr
    {p p' q q' : CuntzProjection (Op := Op)}
    (hpp' : projectionEquivalent p.val p'.val)
    (hqq' : projectionEquivalent q.val q'.val) :
    projectionPreorder p q ↔ projectionPreorder p' q' := by
  constructor
  · intro hpq
    exact projectionPreorder_trans (projectionPreorder_trans hpp'.2 hpq) hqq'.1
  · intro hpq
    exact projectionPreorder_trans (projectionPreorder_trans hpp'.1 hpq) hqq'.2

/-- The quotient map to `CuntzCu` is monotone. -/
@[rep_depth operator]
theorem CuntzCu_mk_monotone :
    Monotone (Quotient.mk (CuntzProjectionSetoid (Op := Op))) :=
  Quotient.mk_monotone (s := CuntzProjectionSetoid (Op := Op))

/-- The quotient order respects projection preorder on representatives. -/
@[rep_depth operator]
theorem CuntzCu_mk_le
    (p q : CuntzProjection (Op := Op))
    (hpq : projectionPreorder p q) :
    (Quotient.mk (CuntzProjectionSetoid (Op := Op)) p : CuntzCu) ≤
      Quotient.mk (CuntzProjectionSetoid (Op := Op)) q :=
  CuntzCu_mk_monotone hpq

/-- Equivalent Cuntz projections define the same quotient class. -/
@[rep_depth operator]
theorem CuntzCu_mk_eq
    {p q : CuntzProjection (Op := Op)}
    (hpq : projectionEquivalent p.val q.val) :
    (Quotient.mk (CuntzProjectionSetoid (Op := Op)) p : CuntzCu) =
      Quotient.mk (CuntzProjectionSetoid (Op := Op)) q := by
  exact Quotient.sound hpq

/-- Equality of quotient classes descends back to projection equivalence. -/
@[rep_depth operator]
theorem CuntzCu_mk_eq_iff
    {p q : CuntzProjection (Op := Op)} :
    (Quotient.mk (CuntzProjectionSetoid (Op := Op)) p : CuntzCu) =
      Quotient.mk (CuntzProjectionSetoid (Op := Op)) q ↔
      projectionEquivalent p.val q.val := by
  constructor
  · exact Quotient.exact
  · exact CuntzCu_mk_eq

/-- The left summand class lies below the orthogonal sum class. -/
@[rep_depth operator]
theorem CuntzCu_left_le_orthogonalSum
    (p q : CuntzProjection (Op := Op))
    (h : projectionOrthogonal p q) :
    (Quotient.mk (CuntzProjectionSetoid (Op := Op)) p : CuntzCu) ≤
      Quotient.mk (CuntzProjectionSetoid (Op := Op)) (orthogonalSum p q h) := by
  exact CuntzCu_mk_le p (orthogonalSum p q h) (left_le_orthogonalSum p q h)

/-- The right summand class lies below the orthogonal sum class. -/
@[rep_depth operator]
theorem CuntzCu_right_le_orthogonalSum
    (p q : CuntzProjection (Op := Op))
    (h : projectionOrthogonal p q) :
    (Quotient.mk (CuntzProjectionSetoid (Op := Op)) q : CuntzCu) ≤
      Quotient.mk (CuntzProjectionSetoid (Op := Op)) (orthogonalSum p q h) := by
  exact CuntzCu_mk_le q (orthogonalSum p q h) (right_le_orthogonalSum p q h)

/-- The left/right orthogonal sum class is the unit class. -/
@[rep_depth operator]
theorem CuntzCu_leftRightOrthogonalSum_eq_unit :
    (Quotient.mk (CuntzProjectionSetoid (Op := Op))
      (orthogonalSum (leftCuntzProjection (C := C)) (rightCuntzProjection (C := C))
        (leftRightCuntzProjection_orthogonal (C := C))) : CuntzCu) =
      Quotient.mk (CuntzProjectionSetoid (Op := Op)) (unitCuntzProjection (Op := Op)) := by
  simpa [leftRightOrthogonalSum_eq_unit] using
    (CuntzCu_mk_eq (C := C)
      (p := orthogonalSum (leftCuntzProjection (C := C)) (rightCuntzProjection (C := C))
        (leftRightCuntzProjection_orthogonal (C := C)))
      (q := unitCuntzProjection (Op := Op))
      (projectionEquivalent_refl (unitCuntzProjection (Op := Op))
        (unitCuntzProjection (Op := Op)).property))

/-- The left/right orthogonal sum class lies below the unit class. -/
@[rep_depth operator]
theorem CuntzCu_leftRightOrthogonalSum_le_unit :
    (Quotient.mk (CuntzProjectionSetoid (Op := Op))
      (orthogonalSum (leftCuntzProjection (C := C)) (rightCuntzProjection (C := C))
        (leftRightCuntzProjection_orthogonal (C := C))) : CuntzCu) ≤
      Quotient.mk (CuntzProjectionSetoid (Op := Op)) (unitCuntzProjection (Op := Op)) := by
  simpa [CuntzCu_leftRightOrthogonalSum_eq_unit] using
    (le_rfl :
      (Quotient.mk (CuntzProjectionSetoid (Op := Op))
        (orthogonalSum (leftCuntzProjection (C := C)) (rightCuntzProjection (C := C))
          (leftRightCuntzProjection_orthogonal (C := C))) : CuntzCu) ≤
        Quotient.mk (CuntzProjectionSetoid (Op := Op))
          (orthogonalSum (leftCuntzProjection (C := C)) (rightCuntzProjection (C := C))
            (leftRightCuntzProjection_orthogonal (C := C))))

/-- The orthogonal sum class lies between the summands and the unit class. -/
@[rep_depth operator]
theorem CuntzCu_orthogonalSum_bounds
    (p q : CuntzProjection (Op := Op))
    (h : projectionOrthogonal p q) :
    (Quotient.mk (CuntzProjectionSetoid (Op := Op)) p : CuntzCu) ≤
      Quotient.mk (CuntzProjectionSetoid (Op := Op)) (orthogonalSum p q h) ∧
    (Quotient.mk (CuntzProjectionSetoid (Op := Op)) q : CuntzCu) ≤
      Quotient.mk (CuntzProjectionSetoid (Op := Op)) (orthogonalSum p q h) ∧
    (Quotient.mk (CuntzProjectionSetoid (Op := Op)) (orthogonalSum p q h) : CuntzCu) ≤
      Quotient.mk (CuntzProjectionSetoid (Op := Op)) (unitCuntzProjection (Op := Op)) := by
  constructor
  · exact CuntzCu_left_le_orthogonalSum p q h
  constructor
  · exact CuntzCu_right_le_orthogonalSum p q h
  · exact CuntzCu_mk_le (orthogonalSum p q h) (unitCuntzProjection (Op := Op)) (by
      change (orthogonalSum p q h).val * 1 = (orthogonalSum p q h).val
      simp)

/-- The quotient class of an orthogonal sum is independent of the order. -/
@[rep_depth operator]
theorem CuntzCu_orthogonalSum_comm
    (p q : CuntzProjection (Op := Op))
    (h : projectionOrthogonal p q) :
    (Quotient.mk (CuntzProjectionSetoid (Op := Op)) (orthogonalSum p q h) : CuntzCu) =
      Quotient.mk (CuntzProjectionSetoid (Op := Op))
        (orthogonalSum q p ⟨h.2, h.1⟩) := by
  simpa [orthogonalSum_comm p q h] using
    (CuntzCu_mk_eq (C := C) (p := orthogonalSum p q h) (q := orthogonalSum q p ⟨h.2, h.1⟩)
      (projectionEquivalent_refl (orthogonalSum p q h).val (orthogonalSum p q h).property))

/-- The quotient class of an orthogonal sum with zero on the left is the original class. -/
@[rep_depth operator]
theorem CuntzCu_orthogonalSum_zero_left
    (p : CuntzProjection (Op := Op)) :
    (Quotient.mk (CuntzProjectionSetoid (Op := Op))
      (orthogonalSum (zeroCuntzProjection (Op := Op)) p
        (zeroProjectionOrthogonal_left (p := p))) : CuntzCu) =
      Quotient.mk (CuntzProjectionSetoid (Op := Op)) p := by
  simpa [orthogonalSum_zero_left] using
    (CuntzCu_mk_eq (C := C)
      (p := orthogonalSum (zeroCuntzProjection (Op := Op)) p
        (zeroProjectionOrthogonal_left (p := p)))
      (q := p)
      (projectionEquivalent_refl p p.2))

/-- The quotient class of an orthogonal sum with zero on the right is the original class. -/
@[rep_depth operator]
theorem CuntzCu_orthogonalSum_zero_right
    (p : CuntzProjection (Op := Op)) :
    (Quotient.mk (CuntzProjectionSetoid (Op := Op))
      (orthogonalSum p (zeroCuntzProjection (Op := Op))
        (zeroProjectionOrthogonal_right (p := p))) : CuntzCu) =
      Quotient.mk (CuntzProjectionSetoid (Op := Op)) p := by
  simpa [orthogonalSum_zero_right] using
    (CuntzCu_mk_eq (C := C)
      (p := orthogonalSum p (zeroCuntzProjection (Op := Op))
        (zeroProjectionOrthogonal_right (p := p)))
      (q := p)
      (projectionEquivalent_refl p p.2))

/-- The quotient class of a pairwise orthogonal triple sum is independent of association. -/
@[rep_depth operator]
theorem CuntzCu_orthogonalSum_assoc
    (p q r : CuntzProjection (Op := Op))
    (hpq : projectionOrthogonal p q)
    (hpr : projectionOrthogonal p r)
    (hqr : projectionOrthogonal q r) :
    (Quotient.mk (CuntzProjectionSetoid (Op := Op))
      (orthogonalSum (orthogonalSum p q hpq) r
        (orthogonalSum_right_orthogonal p q r hpq hpr hqr)) : CuntzCu) =
      Quotient.mk (CuntzProjectionSetoid (Op := Op))
        (orthogonalSum p (orthogonalSum q r hqr)
          (orthogonalSum_left_orthogonal p q r hpq hpr hqr)) := by
  simpa [orthogonalSum_assoc p q r hpq hpr hqr] using
    (CuntzCu_mk_eq (C := C)
      (p := orthogonalSum (orthogonalSum p q hpq) r
        (orthogonalSum_right_orthogonal p q r hpq hpr hqr))
      (q := orthogonalSum p (orthogonalSum q r hqr)
        (orthogonalSum_left_orthogonal p q r hpq hpr hqr))
      (projectionEquivalent_refl
        (orthogonalSum (orthogonalSum p q hpq) r
          (orthogonalSum_right_orthogonal p q r hpq hpr hqr)).val
        (orthogonalSum (orthogonalSum p q hpq) r
          (orthogonalSum_right_orthogonal p q r hpq hpr hqr)).property))


/-- The left Cuntz projection class lies below the unit class. -/
@[rep_depth operator]
theorem leftCuntzCu_le_unit :
    (Quotient.mk (CuntzProjectionSetoid (Op := Op)) (leftCuntzProjection (C := C))) ≤
      Quotient.mk (CuntzProjectionSetoid (Op := Op)) (unitCuntzProjection (Op := Op)) := by
  exact CuntzCu_mk_monotone (leftRangeProjection_le_unit (C := C))

/-- The right Cuntz projection class lies below the unit class. -/
@[rep_depth operator]
theorem rightCuntzCu_le_unit :
    (Quotient.mk (CuntzProjectionSetoid (Op := Op)) (rightCuntzProjection (C := C))) ≤
      Quotient.mk (CuntzProjectionSetoid (Op := Op)) (unitCuntzProjection (Op := Op)) := by
  exact CuntzCu_mk_monotone (rightRangeProjection_le_unit (C := C))

end CuntzO2Carrier

/-- Candidate Majorana/Clifford operators generated from a Cuntz shift. -/
@[rep_depth operator]
class PhaseAxisCarrier (Op : Type*) where
  phaseAxis : Op

namespace PhaseAxisCarrier

variable {Op : Type*}

end PhaseAxisCarrier

/-- Canonical phase-axis instance for the doubled real operator carrier. -/
instance doubledSpaceEndPhaseAxis
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    PhaseAxisCarrier (DoubledSpace E →L[ℝ] DoubledSpace E) where
  phaseAxis := clockAxis (E := E)

/-- Candidate Majorana/Clifford operators generated from a Cuntz shift. -/
@[rep_depth operator]
structure CuntzMajoranaCandidates
    (Op : Type*) [Ring Op] [StarRing Op] [PhaseAxisCarrier Op] where
  cuntz : CuntzO2Carrier Op

namespace CuntzMajoranaCandidates

variable {Op : Type*} [Ring Op] [StarRing Op] [PhaseAxisCarrier Op]
variable (M : CuntzMajoranaCandidates Op)

/-- Canonical phase axis supplied by the carrier instance. -/
@[rep_depth operator]
def carrierPhaseAxis : Op :=
  PhaseAxisCarrier.phaseAxis (Op := Op)

/-- Candidate `e_1 = S_1 + S_1*`. -/
@[rep_depth operator]
def e1 : Op :=
  M.cuntz.S_left + star M.cuntz.S_left

/-- Candidate `e_2 = phaseAxis * (S_1 - S_1*)`. -/
@[rep_depth operator]
def e2 : Op :=
  carrierPhaseAxis (Op := Op) * (M.cuntz.S_left - star M.cuntz.S_left)

@[rep_depth operator]
theorem e1_eq :
    M.e1 = M.cuntz.S_left + star M.cuntz.S_left :=
  rfl

@[rep_depth operator]
theorem e2_eq :
    M.e2 = carrierPhaseAxis (Op := Op) * (M.cuntz.S_left - star M.cuntz.S_left) :=
  rfl

end CuntzMajoranaCandidates

/-- Anticommutator in an abstract ring. -/
@[rep_depth operator]
def anticommutator
    {Op : Type*} [Add Op] [Mul Op]
    (x y : Op) : Op :=
  x * y + y * x

/--
Witness that the Cuntz Majorana candidates satisfy the intended Clifford/CAR laws.

This is intentionally not derived from the Cuntz relations alone.
-/
@[rep_depth operator]
structure MajoranaCARWitness
    (Op : Type*) [Ring Op] [StarRing Op] [PhaseAxisCarrier Op]
    (M : CuntzMajoranaCandidates Op) where
  e1_square :
    M.e1 * M.e1 = 1

  e2_square :
    M.e2 * M.e2 = 1

  anticommute :
    anticommutator M.e1 M.e2 = 0

namespace MajoranaCARWitness

variable {Op : Type*} [Ring Op] [StarRing Op] [SMul ℂ Op] [PhaseAxisCarrier Op]
variable {M : CuntzMajoranaCandidates Op}

/--
Construct a `MajoranaCARWitness` from explicit proof terms.

This is the honest constructor: rather than carrying `e1_square`, `e2_square`,
`anticommute` as opaque hypothesis fields, this bundles them as a single
theorem-backed package.  Downstream users can still access each component
via the structure fields.
-/
@[rep_depth operator]
def ofProofs (h1 : M.e1 * M.e1 = 1) (h2 : M.e2 * M.e2 = 1)
    (h3 : anticommutator M.e1 M.e2 = 0) : MajoranaCARWitness Op M := by
  exact ⟨h1, h2, h3⟩

/--
Construct a `MajoranaCARWitness` from a single bundled proof of all three
Clifford/CAR laws.  Uses conjunction instead of `Prod` since the components
are `Prop`, not `Type`.
-/
@[rep_depth operator]
def ofBundle (h : (M.e1 * M.e1 = 1) ∧ (M.e2 * M.e2 = 1) ∧ (anticommutator M.e1 M.e2 = 0)) :
    MajoranaCARWitness Op M := by
  exact ⟨h.1, h.2.1, h.2.2⟩

end MajoranaCARWitness

/-- Canonical real doubled phase-axis readout for the Cuntz/Majorana lane. -/
@[rep_depth operator]
noncomputable def canonicalRealDoubledPhaseAxis
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    DoubledSpace E →L[ℝ] DoubledSpace E :=
  clockAxis (E := E)

@[rep_depth operator, simp]
theorem canonicalRealDoubledPhaseAxis_eq_clockAxis
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    canonicalRealDoubledPhaseAxis (E := E) = clockAxis (E := E) :=
  rfl

@[rep_depth operator, simp]
theorem canonicalRealDoubledPhaseAxis_eq_complex_i
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    canonicalRealDoubledPhaseAxis (E := E) = complex_i (E := E) := by
  simpa [canonicalRealDoubledPhaseAxis] using
    InfoGeometry.Canonical.BilingualRealHestenesDictionary.realPhaseAxis_eq_complex_i
      (E := E)

@[rep_depth operator]
theorem canonicalRealDoubledPhaseAxis_sq_eq_neg_id
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    (canonicalRealDoubledPhaseAxis (E := E)).comp (canonicalRealDoubledPhaseAxis (E := E))
      = -(ContinuousLinearMap.id ℝ (DoubledSpace E)) := by
  simpa [canonicalRealDoubledPhaseAxis] using
    InfoGeometry.Canonical.BilingualRealHestenesDictionary.realPhaseAxis_sq (E := E)

/-- The generic carrier readout specializes to the canonical clock axis on the doubled carrier. -/
@[rep_depth operator, simp]
theorem doubledSpace_carrierPhaseAxis_eq_clockAxis
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    CuntzMajoranaCandidates.carrierPhaseAxis (Op := DoubledSpace E →L[ℝ] DoubledSpace E)
      = clockAxis (E := E) :=
  rfl

/-- Real-doubled specialization of the Cuntz/Majorana lane. -/
@[rep_depth operator]
structure RealDoubledCuntzMajoranaPacket
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] where
  cuntz : CuntzO2Carrier (Op := DoubledSpace E →L[ℝ] DoubledSpace E)

namespace RealDoubledCuntzMajoranaPacket

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable (M : RealDoubledCuntzMajoranaPacket (E := E))

local notation "EndH" => DoubledSpace E →L[ℝ] DoubledSpace E

/-- The phase axis is derived from the canonical real doubled lane. -/
@[rep_depth operator]
noncomputable def realDoubledPhaseAxis (M : RealDoubledCuntzMajoranaPacket (E := E)) : EndH :=
  canonicalRealDoubledPhaseAxis (E := E)

/-- The phase axis readout is the canonical clock axis. -/
@[rep_depth operator, simp]
theorem realDoubledPhaseAxis_eq_clockAxis :
    M.realDoubledPhaseAxis = clockAxis (E := E) := by
  simpa [RealDoubledCuntzMajoranaPacket.realDoubledPhaseAxis] using
    canonicalRealDoubledPhaseAxis_eq_clockAxis (E := E)

/-- The phase axis readout is the canonical real doubled complex structure. -/
@[rep_depth operator, simp]
theorem realDoubledPhaseAxis_eq_complex_i :
    M.realDoubledPhaseAxis = complex_i (E := E) := by
  simpa [RealDoubledCuntzMajoranaPacket.realDoubledPhaseAxis] using
    canonicalRealDoubledPhaseAxis_eq_complex_i (E := E)

/-- Convert the specialized packet to the generic Cuntz/Majorana candidate. -/
@[rep_depth operator]
noncomputable def toCuntzMajoranaCandidates :
    CuntzMajoranaCandidates (Op := EndH) where
  cuntz := M.cuntz

/-- The specialized packet uses the canonical `e₂` construction. -/
@[rep_depth operator, simp]
theorem e2_eq_canonical :
    (M.toCuntzMajoranaCandidates).e2 =
      canonicalRealDoubledPhaseAxis (E := E) *
        (M.cuntz.S_left - star M.cuntz.S_left) := by
  rfl

end RealDoubledCuntzMajoranaPacket

/-- A bounded spectral-triple-style socket over a Cuntz/Cantor carrier. -/
@[rep_depth operator]
structure CuntzCantorSpectralTriple
    (Op H : Type*) [Ring Op] [StarRing Op] [NormedAddCommGroup H] [NormedSpace ℂ H]
    [SMul Op H] where
  cuntz : CuntzO2Carrier Op

  /-- Representation of the binary Cantor cylinder algebra in the operator carrier. -/
  cylinderRepresentation : (n : Nat) -> BinaryCylinder n -> Op

  /-- Bounded placeholder for a Dirac/supercharge operator. -/
  dirac : H →L[ℂ] H

  /-- Representation action used to state bounded commutator data. -/
  representedAction : Op -> H →L[ℂ] H

  /-- Supplied bounded-commutator condition for represented cylinder operators. -/
  boundedCommutatorWitness : Prop
  boundedCommutatorCertified : boundedCommutatorWitness

  /-- Supplied compact-resolvent or summability condition. -/
  compactResolventOrSummability : Prop
  compactResolventOrSummabilityCertified : compactResolventOrSummability

  /-- Spectral dimension readout supplied by the concrete model. -/
  spectralDimension : ℝ

  /-- Optional calibration to the middle-thirds Cantor dimension. -/
  cantorDimensionCalibration :
    spectralDimension = Real.log 2 / Real.log 3

namespace CuntzCantorSpectralTriple

variable {Op H : Type*} [Ring Op] [StarRing Op]
variable [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Op H]
variable (T : CuntzCantorSpectralTriple Op H)

/-- The left Cuntz range projection of the spectral-triple carrier. -/
@[rep_depth operator]
def leftCylinderProjection : Op :=
  T.cuntz.leftRangeProjection

/-- The right Cuntz range projection of the spectral-triple carrier. -/
@[rep_depth operator]
def rightCylinderProjection : Op :=
  T.cuntz.rightRangeProjection

/-- Cylinder projections cover the binary boundary at the first level. -/
@[rep_depth operator]
theorem firstLevelCylinder_sum_one :
    T.leftCylinderProjection + T.rightCylinderProjection = 1 := by
  exact T.cuntz.rangeProjection_sum_one

/-- The supplied spectral dimension equals the middle-thirds Cantor dimension. -/
@[rep_depth operator]
theorem spectralDimension_eq_middleThirdsCantor :
    T.spectralDimension = Real.log 2 / Real.log 3 :=
  T.cantorDimensionCalibration

/-- Re-export the bounded-commutator witness. -/
@[rep_depth operator]
theorem boundedCommutator_holds :
    T.boundedCommutatorWitness :=
  T.boundedCommutatorCertified

/-- Re-export the compact-resolvent/summability witness. -/
@[rep_depth operator]
theorem compactResolventOrSummability_holds :
    T.compactResolventOrSummability :=
  T.compactResolventOrSummabilityCertified

end CuntzCantorSpectralTriple

/--
Connection socket from a combinatorial `ErlangenNet` boundary to a Cuntz/Cantor
spectral triple.
-/
@[rep_depth operator]
structure ErlangenNetCuntzRealization
    (Alg Frame Sym Label Op H : Type*) [Ring Op] [StarRing Op]
    [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Op H] where
  net : IteratedObservableSectorization Alg Frame Sym BinarySector Label
  triple : CuntzCantorSpectralTriple Op H

  /-- Boundary-code prefixing is represented by the left Cuntz shift. -/
  leftPrefixRealization : Prop
  leftPrefixRealizationCertified : leftPrefixRealization

  /-- Boundary-code prefixing is represented by the right Cuntz shift. -/
  rightPrefixRealization : Prop
  rightPrefixRealizationCertified : rightPrefixRealization

namespace ErlangenNetCuntzRealization

variable {Alg Frame Sym Label Op H : Type*} [Ring Op] [StarRing Op]
variable [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Op H]
variable (R : ErlangenNetCuntzRealization Alg Frame Sym Label Op H)

/-- Re-export the left-prefix realization witness. -/
@[rep_depth operator]
theorem leftPrefixRealization_holds :
    R.leftPrefixRealization :=
  R.leftPrefixRealizationCertified

/-- Re-export the right-prefix realization witness. -/
@[rep_depth operator]
theorem rightPrefixRealization_holds :
    R.rightPrefixRealization :=
  R.rightPrefixRealizationCertified

/-- The Cuntz realization gives the first-level boundary decomposition. -/
@[rep_depth operator]
theorem realized_firstLevelCylinder_sum_one :
    R.triple.leftCylinderProjection + R.triple.rightCylinderProjection = 1 :=
  R.triple.firstLevelCylinder_sum_one

end ErlangenNetCuntzRealization

end InfoGeometry.Topology
