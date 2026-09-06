import Mathlib.Tactic.Ring

/-!
# InfoGeometry.Projective.SplitOctonions.BektasMatrix

Concrete Bektaş `2 × 2` quaternion-block model for split-octonion coordinates.

This file defines:
1. an unrolled real-quaternion coordinate type;
2. the Bektaş cell `(q1,q2)`;
3. block determinant and block trace readouts;
4. coordinate identities showing the split-signature determinant expression.

No wrappers. No `sorry`.
-/

namespace InfoGeometry.Projective.SplitOctonions.BektasMatrix

variable {R : Type*} [CommRing R]

/-- Unrolled real-quaternion coordinates. -/
structure Quat (R : Type*) where
  r : R
  i : R
  j : R
  k : R

namespace Quat

/-- Positive-definite quaternion norm polynomial. -/
def norm (q : Quat R) : R :=
  q.r ^ 2 + q.i ^ 2 + q.j ^ 2 + q.k ^ 2

/-- Quaternion conjugation in coordinates. -/
def conj (q : Quat R) : Quat R :=
  { r := q.r, i := -q.i, j := -q.j, k := -q.k }

/-- Real scalar projection (real part). -/
def realPart (q : Quat R) : R := q.r

end Quat

/--
Bektaş split-octonion cell:
pair of quaternions `(q1,q2)` corresponding to the block model.
-/
structure BektasCell (R : Type*) where
  q1 : Quat R
  q2 : Quat R

namespace BektasCell

/--
Formal block determinant:
`det = norm(q1) - norm(q2)`.
-/
def blockDet (X : BektasCell R) : R :=
  X.q1.norm - X.q2.norm

/-- Formal scalar trace readout: `2 * Re(q1)`. -/
def blockTrace (X : BektasCell R) : R :=
  X.q1.realPart + X.q1.realPart

/--
Block determinant equals the explicit split-signature coordinate polynomial.
-/
theorem blockDet_is_split_signature (X : BektasCell R) :
    X.blockDet =
      (X.q1.r ^ 2 + X.q1.i ^ 2 + X.q1.j ^ 2 + X.q1.k ^ 2) -
      (X.q2.r ^ 2 + X.q2.i ^ 2 + X.q2.j ^ 2 + X.q2.k ^ 2) := by
  unfold blockDet Quat.norm
  ring

/--
Block trace isolates the longitudinal scalar coordinate.
-/
theorem trace_is_longitudinal_scalar (X : BektasCell R) :
    X.blockTrace = 2 * X.q1.r := by
  unfold blockTrace Quat.realPart
  ring

end BektasCell

end InfoGeometry.Projective.SplitOctonions.BektasMatrix

