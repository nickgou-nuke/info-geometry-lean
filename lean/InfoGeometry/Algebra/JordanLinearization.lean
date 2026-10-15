import Mathlib.Algebra.Jordan.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
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
  have hadd (f g : AddMonoid.End J) : (f + g) y = f y + g y := rfl
  have hsub (f g : AddMonoid.End J) : (f - g) y = f y - g y := rfl
  have hmul (a b : J) :
      (L a * L b) y = a * (b * y) := by
    change a * (b * y) = a * (b * y)
    rfl
  have hy : ((x * ((x * z) * y) - (x * z) * (x * y)) +
      (x * ((z * x) * y) - (z * x) * (x * y)) +
      (z * ((x * x) * y) - (x * x) * (z * y))) = 0 := by
    have hyraw :
        ((L x * L (x * z) - L (x * z) * L x) +
          (L x * L (z * x) - L (z * x) * L x) +
          (L z * L (x * x) - L (x * x) * L z)) y = 0 := by
      simpa [Ring.lie_def] using hy2raw
    simpa only [hadd, hsub, hmul] using hyraw
  simp [mul_comm] at hy ⊢
  abel_nf at hy
  rw [← sub_eq_zero]
  have hneg := congrArg Neg.neg hy
  abel_nf at hneg ⊢
  exact hneg

end InfoGeometry.Algebra.Jordan
