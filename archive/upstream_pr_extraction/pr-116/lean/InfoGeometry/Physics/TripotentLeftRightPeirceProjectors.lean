import InfoGeometry.Physics.TripotentAdjointDerivation
import Mathlib.Tactic.NoncommRing

/-!
# Left/right multiplication for a tripotent

This owner stays at the operator level.  It records the two commuting
regular actions and their tripotency; Peirce-sector grouping is deliberately
left to a later owner.
-/

namespace InfoGeometry.Physics.Algebra

variable {A : Type*} [Ring A] [Algebra ℝ A]

section
variable {e : A} (he : e * e * e = e)

lemma leftMulLinear_cube (he : e * e * e = e) :
    leftMulLinear e * leftMulLinear e * leftMulLinear e = leftMulLinear e := by
  ext x
  change e * (e * (e * x)) = e * x
  calc
    e * (e * (e * x)) = (e * e * e) * x := by noncomm_ring
    _ = e * x := by rw [he]

lemma rightMulLinear_cube (he : e * e * e = e) :
    rightMulLinear e * rightMulLinear e * rightMulLinear e = rightMulLinear e := by
  ext x
  change ((x * e) * e) * e = x * e
  calc
    ((x * e) * e) * e = x * (e * e * e) := by noncomm_ring
    _ = x * e := by rw [he]

lemma leftMulLinear_comm_rightMulLinear :
    leftMulLinear e * rightMulLinear e = rightMulLinear e * leftMulLinear e := by
  ext x
  change e * (x * e) = (e * x) * e
  exact (mul_assoc e x e).symm

end

end InfoGeometry.Physics.Algebra
