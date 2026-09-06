import Mathlib.Algebra.Jordan.Basic
import Mathlib.Tactic

namespace InfoGeometry.Algebra.Jordan

local notation "L" => AddMonoid.End.mulLeft

/--
A genuine non-associative linearization of the commutative Jordan identity.

This is proved from mathlib's non-associative Jordan theorem
`two_nsmul_lie_lmul_lmul_add_add_eq_zero`, not from associativity and not from
an added proposition field.  The hypotheses are the standard mathlib carrier for
linear commutative Jordan rings: `NonUnitalNonAssocCommRing`, `IsCommJordan`,
and additive torsion-freeness to cancel the outer factor `2`.
-/
lemma linearized_jordan_identity
    (J : Type*) [NonUnitalNonAssocCommRing J] [IsCommJordan J]
    [IsAddTorsionFree J]
    (x y z : J) :
    (x * x) * (y * z) + 2 • ((x * z) * (y * x)) =
    2 • (x * (y * (x * z))) + z * (y * (x * x)) := by
  have h0 := two_nsmul_lie_lmul_lmul_add_add_eq_zero (A := J) x x z
  have hy2raw := congrArg (fun f : AddMonoid.End J => f y) h0
  have hy2 : 2 • ((x * ((x * z) * y) - (x * z) * (x * y)) +
      (x * ((z * x) * y) - (z * x) * (x * y)) +
      (z * ((x * x) * y) - (x * x) * (z * y))) = 0 := by
    simpa [Ring.lie_def, nsmul_add, AddMonoid.End.mulLeft] using hy2raw
  have hy : ((x * ((x * z) * y) - (x * z) * (x * y)) +
      (x * ((z * x) * y) - (z * x) * (x * y)) +
      (z * ((x * x) * y) - (x * x) * (z * y))) = 0 := by
    exact (nsmul_eq_zero_iff_right (M := J) (n := 2) (by norm_num)).mp hy2
  simp [mul_comm] at hy ⊢
  abel_nf at hy
  rw [← sub_eq_zero]
  have hneg := congrArg Neg.neg hy
  abel_nf at hneg ⊢
  exact hneg

end InfoGeometry.Algebra.Jordan
