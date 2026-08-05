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

/-! The Cuntz `O₂` carrier is the `N := 2` instance of the generic owner. -/
abbrev CuntzO2Carrier
    (Op : Type*) [Ring Op] [StarRing Op] :=
  InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op

namespace CuntzO2Carrier

variable {Op : Type*} [Ring Op] [StarRing Op]
variable (C : CuntzO2Carrier Op)

/-- The left branch is the canonical zero-indexed Cuntz generator. -/
@[rep_depth operator]
def S_left : Op := C.S 0

/-- The right branch is the canonical one-indexed Cuntz generator. -/
@[rep_depth operator]
def S_right : Op := C.S 1

theorem left_isometry : star C.S_left * C.S_left = 1 := by
  simpa [S_left] using C.isometry 0 0

theorem right_isometry : star C.S_right * C.S_right = 1 := by
  simpa [S_right] using C.isometry 1 1

theorem orthogonal_ranges :
    star C.S_left * C.S_right = 0 ∧ star C.S_right * C.S_left = 0 := by
  constructor
  · simpa [S_left, S_right] using C.isometry 0 1
  · simpa [S_left, S_right] using C.isometry 1 0

theorem range_sum :
    C.S_left * star C.S_left + C.S_right * star C.S_right = 1 := by
  simpa [S_left, S_right] using
    InfoGeometry.Algebra.Cuntz.CuntzNAlgebra.range_sum C

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
  exact range_sum C

theorem leftRangeProjection_star :
    star C.leftRangeProjection = C.leftRangeProjection := by
  unfold leftRangeProjection
  rw [star_mul, star_star]

theorem rightRangeProjection_star :
    star C.rightRangeProjection = C.rightRangeProjection := by
  unfold rightRangeProjection
  rw [star_mul, star_star]

section ProjectionSubequiv

variable {Op : Type*} [Ring Op]

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

end ProjectionSubequiv

/-- The left Cuntz range projection is subequivalent to the unit. -/
@[rep_depth operator]
theorem leftRangeProjection_subequiv_one :
    projectionSubequiv C.leftRangeProjection 1 := by
  unfold projectionSubequiv
  simp

/-- The right Cuntz range projection is subequivalent to the unit. -/
@[rep_depth operator]
theorem rightRangeProjection_subequiv_one :
    projectionSubequiv C.rightRangeProjection 1 := by
  unfold projectionSubequiv
  simp

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

variable {Op : Type*} [Ring Op]

/-- A Cuntz projection remembers its underlying operator. -/
@[rep_depth operator]
abbrev val (p : CuntzProjection (Op := Op)) : Op := p.1

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

section ProjectionPreorder

variable {Op : Type*} [Ring Op]

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

end ProjectionPreorder

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

section ProjectionOrthogonal

variable {Op : Type*} [Ring Op]

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
            simp [hp, hq]

/-- Orthogonal sum is commutative when the orthogonality data is swapped. -/
@[rep_depth operator]
theorem orthogonalSum_comm
    (p q : CuntzProjection (Op := Op))
    (h : projectionOrthogonal p q) :
    orthogonalSum p q h = orthogonalSum q p ⟨h.2, h.1⟩ := by
  apply Subtype.ext
  change p.val + q.val = q.val + p.val
  simp [add_comm]

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

end ProjectionOrthogonal

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

section ProjectionEquivalence

variable {Op : Type*} [Ring Op]

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

end ProjectionEquivalence

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

section ProjectionEquivalence

variable {Op : Type*} [Ring Op]

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
  rw [orthogonalSum_proof_irrel p q h h']

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

end ProjectionEquivalence

section CuntzCuOrder

variable {Op : Type*} [Ring Op]

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

end CuntzCuOrder

/-- The left/right orthogonal sum class is the unit class. -/
@[rep_depth operator]
theorem CuntzCu_leftRightOrthogonalSum_eq_unit :
    (Quotient.mk (CuntzProjectionSetoid (Op := Op))
      (orthogonalSum (leftCuntzProjection (C := C)) (rightCuntzProjection (C := C))
        (leftRightCuntzProjection_orthogonal (C := C))) : CuntzCu) =
      Quotient.mk (CuntzProjectionSetoid (Op := Op)) (unitCuntzProjection (Op := Op)) := by
  rw [leftRightOrthogonalSum_eq_unit]

/-- The left/right orthogonal sum class lies below the unit class. -/
@[rep_depth operator]
theorem CuntzCu_leftRightOrthogonalSum_le_unit :
    (Quotient.mk (CuntzProjectionSetoid (Op := Op))
      (orthogonalSum (leftCuntzProjection (C := C)) (rightCuntzProjection (C := C))
        (leftRightCuntzProjection_orthogonal (C := C))) : CuntzCu) ≤
      Quotient.mk (CuntzProjectionSetoid (Op := Op)) (unitCuntzProjection (Op := Op)) := by
  rw [CuntzCu_leftRightOrthogonalSum_eq_unit]

section CuntzCuOrthogonalSumOrder

variable {Op : Type*} [Ring Op]

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
  rw [orthogonalSum_comm p q h]

/-- The quotient class of an orthogonal sum with zero on the left is the original class. -/
@[rep_depth operator]
theorem CuntzCu_orthogonalSum_zero_left
    (p : CuntzProjection (Op := Op)) :
    (Quotient.mk (CuntzProjectionSetoid (Op := Op))
      (orthogonalSum (zeroCuntzProjection (Op := Op)) p
        (zeroProjectionOrthogonal_left (p := p))) : CuntzCu) =
      Quotient.mk (CuntzProjectionSetoid (Op := Op)) p := by
  rw [orthogonalSum_zero_left]

/-- The quotient class of an orthogonal sum with zero on the right is the original class. -/
@[rep_depth operator]
theorem CuntzCu_orthogonalSum_zero_right
    (p : CuntzProjection (Op := Op)) :
    (Quotient.mk (CuntzProjectionSetoid (Op := Op))
      (orthogonalSum p (zeroCuntzProjection (Op := Op))
        (zeroProjectionOrthogonal_right (p := p))) : CuntzCu) =
      Quotient.mk (CuntzProjectionSetoid (Op := Op)) p := by
  rw [orthogonalSum_zero_right]

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
  rw [orthogonalSum_assoc p q r hpq hpr hqr]

end CuntzCuOrthogonalSumOrder


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

/-- A finite Cantor/Krein sector is a binary cylinder address together with a chirality bit. -/
@[rep_depth operator]
abbrev FiniteCantorKreinSector (n : Nat) :=
  BinaryCylinder n × Bool

/-- Completed finite-sector selections form the powerset lattice of concrete sectors. -/
@[rep_depth operator]
abbrev FiniteCantorKreinSectorSet (n : Nat) :=
  Set (FiniteCantorKreinSector n)

/-- Join of finite Cantor/Krein sector selections is union. -/
@[rep_depth operator]
theorem finiteCantorKreinSectorSet_sup_eq_union
    {n : Nat} (P Q : FiniteCantorKreinSectorSet n) :
    P ⊔ Q = P ∪ Q := by
  rfl

/-- Meet of finite Cantor/Krein sector selections is intersection. -/
@[rep_depth operator]
theorem finiteCantorKreinSectorSet_inf_eq_inter
    {n : Nat} (P Q : FiniteCantorKreinSectorSet n) :
    P ⊓ Q = P ∩ Q := by
  rfl

/-- Arbitrary join of finite Cantor/Krein sector selections is set union. -/
@[rep_depth operator]
theorem finiteCantorKreinSectorSet_sSup_eq_sUnion
    {n : Nat} (S : Set (FiniteCantorKreinSectorSet n)) :
    sSup S = ⋃₀ S := by
  rfl

/-- Arbitrary meet of finite Cantor/Krein sector selections is set intersection. -/
@[rep_depth operator]
theorem finiteCantorKreinSectorSet_sInf_eq_sInter
    {n : Nat} (S : Set (FiniteCantorKreinSectorSet n)) :
    sInf S = ⋂₀ S := by
  rfl

/-- Indexed join of finite Cantor/Krein sector selections is indexed union. -/
@[rep_depth operator]
theorem finiteCantorKreinSectorSet_iSup_eq_iUnion
    {ι : Sort u} {n : Nat} (S : ι → FiniteCantorKreinSectorSet n) :
    (⨆ i, S i) = ⋃ i, S i := by
  rfl

/-- Indexed meet of finite Cantor/Krein sector selections is indexed intersection. -/
@[rep_depth operator]
theorem finiteCantorKreinSectorSet_iInf_eq_iInter
    {ι : Sort u} {n : Nat} (S : ι → FiniteCantorKreinSectorSet n) :
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

/-- Self-similar sectors are fixed points of a monotone refinement operator. -/
@[rep_depth operator]
abbrev SelfSimilarSectors {L : Type u} [CompleteLattice L] (R : L →o L) :=
  Function.fixedPoints R

/-- Knaster--Tarski: fixed sectors of a monotone map form a complete lattice. -/
@[rep_depth operator]
noncomputable def selfSimilarSectorsCompleteLattice
    {L : Type u} [CompleteLattice L] (R : L →o L) :
    CompleteLattice (SelfSimilarSectors R) :=
  fixedPoints.completeLattice R

/-- Membership in the self-similar sector type is exactly the fixed-point equation. -/
@[rep_depth operator]
theorem selfSimilarSector_isFixed
    {L : Type u} [CompleteLattice L] (R : L →o L) (P : SelfSimilarSectors R) :
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

/-- Sector selections over the existing concrete Cuntz projection subtype. -/
@[rep_depth operator]
abbrev CuntzProjectionSectorSet
    {Op : Type u} [Ring Op] [StarRing Op] :=
  Set (CuntzO2Carrier.CuntzProjection (Op := Op))

/-- Arbitrary joins in the Cuntz projection sector powerset are unions. -/
@[rep_depth operator]
theorem CuntzProjectionSectorSet_iSup_eq_iUnion
    {Op : Type u} [Ring Op] [StarRing Op] {ι : Sort v}
    (S : ι → CuntzProjectionSectorSet (Op := Op)) :
    (⨆ i, S i) = ⋃ i, S i := by
  rfl

/-- Arbitrary meets in the Cuntz projection sector powerset are intersections. -/
@[rep_depth operator]
theorem CuntzProjectionSectorSet_iInf_eq_iInter
    {Op : Type u} [Ring Op] [StarRing Op] {ι : Sort v}
    (S : ι → CuntzProjectionSectorSet (Op := Op)) :
    (⨅ i, S i) = ⋂ i, S i := by
  rfl

end CompleteLatticeSectorCompletion

/-- Candidate Majorana/Clifford operators generated from a Cuntz shift. -/
@[rep_depth operator]
class PhaseAxisCarrier (Op : Type*) where
  phaseAxis : Op


/-- Canonical phase-axis instance for the doubled real operator carrier. -/
instance doubledSpaceEndPhaseAxis
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    PhaseAxisCarrier (DoubledSpace E →L[ℝ] DoubledSpace E) where
  phaseAxis := clockAxis (E := E)

@[rep_depth operator]
abbrev CuntzMajoranaCandidates
    (Op : Type*) [Ring Op] [StarRing Op] [PhaseAxisCarrier Op] :=
  CuntzO2Carrier Op

namespace CuntzMajoranaCandidates

variable {Op : Type*} [Ring Op] [StarRing Op] [PhaseAxisCarrier Op]
variable (M : CuntzMajoranaCandidates Op)

abbrev cuntz (M : CuntzMajoranaCandidates Op) : CuntzO2Carrier Op := M

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

/-- The first Cuntz Majorana candidate `e₁ = S + S*` is self-adjoint. -/
@[rep_depth operator]
theorem e1_star_eq_self :
    star M.e1 = M.e1 := by
  simp [e1, add_comm]

/-- The first Cuntz Majorana candidate is self-adjoint in Mathlib's `IsSelfAdjoint` API. -/
@[rep_depth operator]
theorem e1_isSelfAdjoint :
    IsSelfAdjoint M.e1 := by
  simpa [IsSelfAdjoint] using M.e1_star_eq_self

/-- The skew part `S - S*` used in the second Cuntz Majorana candidate is skew-adjoint. -/
@[rep_depth operator]
theorem leftShiftSkewPart_star_eq_neg :
    star (M.cuntz.S_left - star M.cuntz.S_left) =
      -(M.cuntz.S_left - star M.cuntz.S_left) := by
  simp [sub_eq_add_neg, add_comm]

/--
The second Cuntz Majorana candidate is self-adjoint once the chosen phase axis is
skew-adjoint and commutes with the skew shift part.
-/
@[rep_depth operator]
theorem e2_star_eq_self_of_phaseAxis
    (hPhaseStar :
      star (carrierPhaseAxis (Op := Op)) = -(carrierPhaseAxis (Op := Op)))
    (hPhaseComm :
      (M.cuntz.S_left - star M.cuntz.S_left) * carrierPhaseAxis (Op := Op) =
        carrierPhaseAxis (Op := Op) * (M.cuntz.S_left - star M.cuntz.S_left)) :
    star M.e2 = M.e2 := by
  unfold e2
  calc
    star (carrierPhaseAxis (Op := Op) * (M.cuntz.S_left - star M.cuntz.S_left))
        = star (M.cuntz.S_left - star M.cuntz.S_left) *
            star (carrierPhaseAxis (Op := Op)) := by
          rw [star_mul]
    _ = (-(M.cuntz.S_left - star M.cuntz.S_left)) *
          (-(carrierPhaseAxis (Op := Op))) := by
          rw [M.leftShiftSkewPart_star_eq_neg, hPhaseStar]
    _ = (M.cuntz.S_left - star M.cuntz.S_left) * carrierPhaseAxis (Op := Op) := by
          noncomm_ring
    _ = carrierPhaseAxis (Op := Op) * (M.cuntz.S_left - star M.cuntz.S_left) := by
          exact hPhaseComm

/--
`IsSelfAdjoint` readback for the second Cuntz Majorana candidate under the same
phase-axis hypotheses.
-/
@[rep_depth operator]
theorem e2_isSelfAdjoint_of_phaseAxis
    (hPhaseStar :
      star (carrierPhaseAxis (Op := Op)) = -(carrierPhaseAxis (Op := Op)))
    (hPhaseComm :
      (M.cuntz.S_left - star M.cuntz.S_left) * carrierPhaseAxis (Op := Op) =
        carrierPhaseAxis (Op := Op) * (M.cuntz.S_left - star M.cuntz.S_left)) :
    IsSelfAdjoint M.e2 := by
  simpa [IsSelfAdjoint] using M.e2_star_eq_self_of_phaseAxis hPhaseStar hPhaseComm

end CuntzMajoranaCandidates

/-- Anticommutator in an abstract ring. -/
@[rep_depth operator]
def anticommutator
    {Op : Type*} [Add Op] [Mul Op]
    (x y : Op) : Op :=
  x * y + y * x

/--
The three Clifford/CAR equations for the Cuntz Majorana candidates.

This is a proposition, not a proof-carrying witness structure.  It remains
explicitly conditional because these equations are not consequences of the
Cuntz relations alone.
-/
@[rep_depth operator]
def MajoranaCARWitness
    (Op : Type*) [Ring Op] [StarRing Op] [PhaseAxisCarrier Op]
    (M : CuntzMajoranaCandidates Op) : Prop :=
  M.e1 * M.e1 = 1 ∧
    M.e2 * M.e2 = 1 ∧
      anticommutator M.e1 M.e2 = 0

namespace MajoranaCARWitness

variable {Op : Type*} [Ring Op] [StarRing Op] [PhaseAxisCarrier Op]
variable {M : CuntzMajoranaCandidates Op}

/-- The first Clifford equation extracted from the conjunction. -/
@[rep_depth operator]
theorem e1_square (h : MajoranaCARWitness Op M) :
    M.e1 * M.e1 = 1 :=
  h.1

/-- The second Clifford equation extracted from the conjunction. -/
@[rep_depth operator]
theorem e2_square (h : MajoranaCARWitness Op M) :
    M.e2 * M.e2 = 1 :=
  h.2.1

/-- The anticommutation equation extracted from the conjunction. -/
@[rep_depth operator]
theorem anticommute (h : MajoranaCARWitness Op M) :
    anticommutator M.e1 M.e2 = 0 :=
  h.2.2

/-- Prove the CAR proposition from the three component equations. -/
@[rep_depth operator]
theorem ofProofs (h1 : M.e1 * M.e1 = 1) (h2 : M.e2 * M.e2 = 1)
    (h3 : anticommutator M.e1 M.e2 = 0) : MajoranaCARWitness Op M :=
  ⟨h1, h2, h3⟩

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
  rw [canonicalRealDoubledPhaseAxis]
  exact InfoGeometry.Canonical.BilingualRealHestenesDictionary.realPhaseAxis_eq_complex_i (E := E)

@[rep_depth operator]
theorem canonicalRealDoubledPhaseAxis_sq_eq_neg_id
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    (canonicalRealDoubledPhaseAxis (E := E)).comp (canonicalRealDoubledPhaseAxis (E := E))
      = -(ContinuousLinearMap.id ℝ (DoubledSpace E)) := by
  rw [canonicalRealDoubledPhaseAxis]
  exact InfoGeometry.Canonical.BilingualRealHestenesDictionary.realPhaseAxis_sq (E := E)

/-- The canonical doubled real phase axis is Hilbert-skew-adjoint. -/
@[rep_depth operator]
theorem canonicalRealDoubledPhaseAxis_star_eq_neg
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    star (canonicalRealDoubledPhaseAxis (E := E)) =
      -(canonicalRealDoubledPhaseAxis (E := E)) := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  apply ContinuousLinearMap.ext
  intro u
  apply ext_inner_left ℝ
  intro v
  rw [ContinuousLinearMap.adjoint_inner_right]
  change
    ⟪canonicalRealDoubledPhaseAxis (E := E) v, u⟫_ℝ =
      ⟪v, -(canonicalRealDoubledPhaseAxis (E := E) u)⟫_ℝ
  rw [inner_neg_right]
  rw [canonicalRealDoubledPhaseAxis]
  exact InfoGeometry.Canonical.TomitaTakesaki.clockAxis_inner_skew (E := E) v u

/-- The generic carrier readout specializes to the canonical clock axis on the doubled carrier. -/
@[rep_depth operator, simp]
theorem doubledSpace_carrierPhaseAxis_eq_clockAxis
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    CuntzMajoranaCandidates.carrierPhaseAxis (Op := DoubledSpace E →L[ℝ] DoubledSpace E)
      = clockAxis (E := E) :=
  rfl

/-- Real-doubled specialization of the Cuntz/Majorana lane. -/
abbrev RealDoubledCuntzMajoranaPacket
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :=
  CuntzO2Carrier (Op := DoubledSpace E →L[ℝ] DoubledSpace E)

namespace RealDoubledCuntzMajoranaPacket

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable (M : RealDoubledCuntzMajoranaPacket (E := E))

/-- Compatibility accessor for the native Cuntz carrier. -/
abbrev cuntz : CuntzO2Carrier (Op := DoubledSpace E →L[ℝ] DoubledSpace E) :=
  M

local notation "EndH" => DoubledSpace E →L[ℝ] DoubledSpace E

/-- The phase axis is derived from the canonical real doubled lane. -/
@[rep_depth operator]
noncomputable def realDoubledPhaseAxis : EndH :=
  canonicalRealDoubledPhaseAxis (E := E)

/-- The phase axis readout is the canonical clock axis. -/
@[rep_depth operator, simp]
theorem realDoubledPhaseAxis_eq_clockAxis :
    realDoubledPhaseAxis (E := E) = clockAxis (E := E) := by
  rw [realDoubledPhaseAxis]
  exact canonicalRealDoubledPhaseAxis_eq_clockAxis (E := E)

/-- The phase axis readout is the canonical real doubled complex structure. -/
@[rep_depth operator, simp]
theorem realDoubledPhaseAxis_eq_complex_i :
    realDoubledPhaseAxis (E := E) = complex_i (E := E) := by
  rw [realDoubledPhaseAxis]
  exact canonicalRealDoubledPhaseAxis_eq_complex_i (E := E)

/-- Convert the specialized packet to the generic Cuntz/Majorana candidate. -/
@[rep_depth operator]
noncomputable def toCuntzMajoranaCandidates :
    CuntzMajoranaCandidates (Op := EndH) :=
  M.cuntz

/-- The specialized packet uses the canonical `e₂` construction. -/
@[rep_depth operator, simp]
theorem e2_eq_canonical :
    (M.toCuntzMajoranaCandidates).e2 =
      canonicalRealDoubledPhaseAxis (E := E) *
        (M.cuntz.S_left - star M.cuntz.S_left) := by
  rfl

/--
The real-doubled Cuntz `e₂` candidate is self-adjoint once the Cuntz skew part
commutes with the canonical doubled real phase axis.
-/
@[rep_depth operator]
theorem e2_isSelfAdjoint_of_commutes_canonicalPhase
    (hComm :
      (M.cuntz.S_left - star M.cuntz.S_left) * canonicalRealDoubledPhaseAxis (E := E) =
        canonicalRealDoubledPhaseAxis (E := E) * (M.cuntz.S_left - star M.cuntz.S_left)) :
    IsSelfAdjoint (M.toCuntzMajoranaCandidates).e2 := by
  exact CuntzMajoranaCandidates.e2_isSelfAdjoint_of_phaseAxis
    (M := M.toCuntzMajoranaCandidates)
    (by
      simpa [CuntzMajoranaCandidates.carrierPhaseAxis, canonicalRealDoubledPhaseAxis] using
        (canonicalRealDoubledPhaseAxis_star_eq_neg (E := E)))
    (by
      simpa [CuntzMajoranaCandidates.carrierPhaseAxis, canonicalRealDoubledPhaseAxis] using hComm)

/--
If the left Cuntz branch commutes with the canonical doubled phase axis, then its
adjoint also commutes with that phase axis.  This is the algebraic propagation
needed in AF/Cantor filtration models where phase-linearity is supplied at the
finite branch level.
-/
@[rep_depth operator]
theorem star_left_commutes_canonicalPhase_of_left_commutes
    (hComm :
      M.cuntz.S_left * canonicalRealDoubledPhaseAxis (E := E) =
        canonicalRealDoubledPhaseAxis (E := E) * M.cuntz.S_left) :
    star M.cuntz.S_left * canonicalRealDoubledPhaseAxis (E := E) =
      canonicalRealDoubledPhaseAxis (E := E) * star M.cuntz.S_left := by
  have hStar :
      star (canonicalRealDoubledPhaseAxis (E := E)) * star M.cuntz.S_left =
        star M.cuntz.S_left * star (canonicalRealDoubledPhaseAxis (E := E)) := by
    simpa only [star_mul] using congrArg star hComm
  rw [canonicalRealDoubledPhaseAxis_star_eq_neg] at hStar
  have hK :
      canonicalRealDoubledPhaseAxis (E := E) * star M.cuntz.S_left =
        star M.cuntz.S_left * canonicalRealDoubledPhaseAxis (E := E) := by
    apply ContinuousLinearMap.ext
    intro x
    have hx := congrArg (fun T : EndH => T x) hStar
    change
      (-(canonicalRealDoubledPhaseAxis (E := E))) (star M.cuntz.S_left x) =
        star M.cuntz.S_left ((-(canonicalRealDoubledPhaseAxis (E := E))) x) at hx
    simp only [ContinuousLinearMap.neg_apply, map_neg] at hx
    exact neg_inj.mp hx
  exact hK.symm

/--
If the left Cuntz branch commutes with the canonical doubled phase axis, then the
skew Majorana branch `S - S*` commutes with that phase axis.
-/
@[rep_depth operator]
theorem leftShiftSkewPart_commutes_canonicalPhase_of_left_commutes
    (hComm :
      M.cuntz.S_left * canonicalRealDoubledPhaseAxis (E := E) =
        canonicalRealDoubledPhaseAxis (E := E) * M.cuntz.S_left) :
    (M.cuntz.S_left - star M.cuntz.S_left) * canonicalRealDoubledPhaseAxis (E := E) =
      canonicalRealDoubledPhaseAxis (E := E) *
        (M.cuntz.S_left - star M.cuntz.S_left) := by
  have hStarComm :
      star M.cuntz.S_left * canonicalRealDoubledPhaseAxis (E := E) =
        canonicalRealDoubledPhaseAxis (E := E) * star M.cuntz.S_left :=
    M.star_left_commutes_canonicalPhase_of_left_commutes hComm
  calc
    (M.cuntz.S_left - star M.cuntz.S_left) * canonicalRealDoubledPhaseAxis (E := E)
        = M.cuntz.S_left * canonicalRealDoubledPhaseAxis (E := E) -
            star M.cuntz.S_left * canonicalRealDoubledPhaseAxis (E := E) := by
          rw [sub_mul]
    _ = canonicalRealDoubledPhaseAxis (E := E) * M.cuntz.S_left -
          canonicalRealDoubledPhaseAxis (E := E) * star M.cuntz.S_left := by
          rw [hComm, hStarComm]
    _ = canonicalRealDoubledPhaseAxis (E := E) *
          (M.cuntz.S_left - star M.cuntz.S_left) := by
          rw [mul_sub]

/--
The real-doubled `e₂` Majorana candidate is self-adjoint from the single
phase-linearity hypothesis that the left Cuntz branch commutes with the
canonical doubled phase axis.
-/
@[rep_depth operator]
theorem e2_isSelfAdjoint_of_left_commutes_canonicalPhase
    (hComm :
      M.cuntz.S_left * canonicalRealDoubledPhaseAxis (E := E) =
        canonicalRealDoubledPhaseAxis (E := E) * M.cuntz.S_left) :
    IsSelfAdjoint (M.toCuntzMajoranaCandidates).e2 := by
  exact M.e2_isSelfAdjoint_of_commutes_canonicalPhase
    (M.leftShiftSkewPart_commutes_canonicalPhase_of_left_commutes hComm)

/--
Hestenes `KLinear` readback for the left Cuntz branch.

This converts the repo-native phase-linearity predicate into the raw
canonical phase-axis commutation used by the Cuntz/Majorana lane.
-/
@[rep_depth operator]
theorem left_commutes_canonicalPhase_of_KLinear
    (hKLinear :
      InfoGeometry.Canonical.HestenesRealStructures.KLinear (E := E) M.cuntz.S_left) :
    M.cuntz.S_left * canonicalRealDoubledPhaseAxis (E := E) =
      canonicalRealDoubledPhaseAxis (E := E) * M.cuntz.S_left := by
  change
    M.cuntz.S_left.comp (canonicalRealDoubledPhaseAxis (E := E)) =
      (canonicalRealDoubledPhaseAxis (E := E)).comp M.cuntz.S_left
  simpa [InfoGeometry.Canonical.HestenesRealStructures.KLinear,
    InfoGeometry.Canonical.BogoliubovTransport.IsPhaseLinear,
    canonicalRealDoubledPhaseAxis] using hKLinear

/--
The real-doubled `e₂` Majorana candidate is self-adjoint from the owner
Hestenes phase-linearity predicate on the left Cuntz branch.
-/
@[rep_depth operator]
theorem e2_isSelfAdjoint_of_left_KLinear
    (hKLinear :
      InfoGeometry.Canonical.HestenesRealStructures.KLinear (E := E) M.cuntz.S_left) :
    IsSelfAdjoint (M.toCuntzMajoranaCandidates).e2 := by
  exact M.e2_isSelfAdjoint_of_left_commutes_canonicalPhase
    (M.left_commutes_canonicalPhase_of_KLinear hKLinear)

end RealDoubledCuntzMajoranaPacket

/-- Native compact-resolvent data for a complex-linear bounded Dirac operator. -/
@[rep_depth operator]
structure ComplexCompactResolventData
    (H : Type*) [NormedAddCommGroup H] [NormedSpace ℂ H] [MulAction ℂ H]
    (D : H →L[ℂ] H) where
  spectralParameter : ℂ
  resolvent : H →L[ℂ] H
  resolvent_comp_shift :
    resolvent.comp
        (D - spectralParameter • ContinuousLinearMap.id ℂ H) =
      ContinuousLinearMap.id ℂ H
  shift_comp_resolvent :
    (D - spectralParameter • ContinuousLinearMap.id ℂ H).comp resolvent =
      ContinuousLinearMap.id ℂ H
  resolvent_compact : IsCompactOperator resolvent

/-- A bounded spectral-triple-style socket over a Cuntz/Cantor carrier. -/
@[rep_depth operator]
structure CuntzCantorSpectralTriple
    (Op H : Type*) [Ring Op] [StarRing Op] [NormedAddCommGroup H] [NormedSpace ℂ H]
    [MulAction ℂ H]
    [SMul Op H] where
  cuntz : CuntzO2Carrier Op

  /-- Representation of the binary Cantor cylinder algebra in the operator carrier. -/
  cylinderRepresentation : (n : Nat) -> BinaryCylinder n -> Op

  /-- Bounded placeholder for a Dirac/supercharge operator. -/
  dirac : H →L[ℂ] H

  /-- Representation action used to state bounded commutator data. -/
  representedAction : Op -> H →L[ℂ] H

  /-- Explicit bounded commutator for every represented cylinder operator. -/
  boundedCommutatorWitness :
    (n : Nat) → BinaryCylinder n → H →L[ℂ] H
  /-- The supplied bounded map is the actual Dirac commutator. -/
  boundedCommutatorCertified :
    ∀ (n : Nat) (word : BinaryCylinder n),
      boundedCommutatorWitness n word =
        dirac.comp (representedAction (cylinderRepresentation n word)) -
          (representedAction (cylinderRepresentation n word)).comp dirac

  /-- Native complex compact-resolvent data for the Dirac operator. -/
  compactResolventOrSummability : ComplexCompactResolventData H dirac

  /-- Spectral dimension readout supplied by the concrete model. -/
  spectralDimension : ℝ

  /-- Optional calibration to the middle-thirds Cantor dimension. -/
  cantorDimensionCalibration :
    spectralDimension = Real.log 2 / Real.log 3

namespace CuntzCantorSpectralTriple

variable {Op H : Type*} [Ring Op] [StarRing Op]
variable [NormedAddCommGroup H] [NormedSpace ℂ H] [MulAction ℂ H] [SMul Op H]
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

/-- Re-export the bounded-commutator formula. -/
@[rep_depth operator]
theorem boundedCommutator_holds
    (n : Nat) (word : BinaryCylinder n) :
    T.boundedCommutatorWitness n word =
      T.dirac.comp (T.representedAction (T.cylinderRepresentation n word)) -
        (T.representedAction (T.cylinderRepresentation n word)).comp T.dirac :=
  T.boundedCommutatorCertified n word

/-- The installed resolvent representative is compact. -/
@[rep_depth operator]
theorem compactResolventOrSummability_holds :
    IsCompactOperator T.compactResolventOrSummability.resolvent :=
  T.compactResolventOrSummability.resolvent_compact

end CuntzCantorSpectralTriple
theorem erlangen_net_left_prefix_realization
    {Alg Frame Sym Label Op H : Type*} [Ring Op] [StarRing Op]
    [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Op H]
    (net : IteratedObservableSectorization Alg Frame Sym BinarySector Label)
    (triple : CuntzCantorSpectralTriple Op H)
    (hLeft :
      triple.cylinderRepresentation 1 (fun _ => BinarySector.plus) =
        triple.cuntz.S_left) :
    triple.cylinderRepresentation 1 (fun _ => BinarySector.plus) =
      triple.cuntz.S_left :=
  hLeft

theorem erlangen_net_right_prefix_realization
    {Alg Frame Sym Label Op H : Type*} [Ring Op] [StarRing Op]
    [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Op H]
    (net : IteratedObservableSectorization Alg Frame Sym BinarySector Label)
    (triple : CuntzCantorSpectralTriple Op H)
    (hRight :
      triple.cylinderRepresentation 1 (fun _ => BinarySector.minus) =
        triple.cuntz.S_right) :
    triple.cylinderRepresentation 1 (fun _ => BinarySector.minus) =
      triple.cuntz.S_right :=
  hRight

end InfoGeometry.Topology
