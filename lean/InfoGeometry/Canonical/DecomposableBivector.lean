import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic

/-!
# Square-zero law for a decomposable bivector

This is a statement about the exterior algebra only. It does not identify the
exterior product with split-octonion multiplication, a Clifford product, a
Klein quadric in a specified four-dimensional space, or a KKT Lie algebra.
The coordinate Klein-quadric realization is handled by its separate owner.
-/

namespace InfoGeometry.Canonical

/-- The exterior square of a decomposable two-vector vanishes. -/
theorem decomposableBivector_square_eq_zero
    {R : Type*} [CommRing R] {V : Type*} [AddCommGroup V] [Module R V]
    (u v : V) :
    (ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R v) *
      (ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R v) = 0 := by
  let e := ExteriorAlgebra.ι R u
  let f := ExteriorAlgebra.ι R v
  have h₁ : e * f * (e * f) = e * (f * (e * f)) := by
    dsimp [e, f]
    exact mul_assoc _ _ _
  have h₂ : f * (e * f) = (f * e) * f := by
    dsimp [e, f]
    exact (mul_assoc _ _ _).symm
  have hswap : f * e = -(e * f) := by
    dsimp [e, f]
    have hadd :
        ExteriorAlgebra.ι R v * ExteriorAlgebra.ι R u +
          ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R v = 0 := by
      exact ExteriorAlgebra.ι_add_mul_swap (R := R) v u
    exact eq_neg_of_add_eq_zero_left hadd
  have h₃ : e * (e * (f * f)) = 0 := by
    rw [← mul_assoc, ExteriorAlgebra.ι_sq_zero, zero_mul]
  calc
    (ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R v) *
        (ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R v) = e * f * (e * f) := rfl
    _ = e * (f * (e * f)) := h₁
    _ = e * ((f * e) * f) := congrArg (e * ·) h₂
    _ = e * ((-(e * f)) * f) := by rw [hswap]
    _ = e * (-(e * (f * f))) := by simp only [neg_mul, mul_assoc]
    _ = 0 := by
      rw [mul_neg, h₃]
      simp

end InfoGeometry.Canonical
