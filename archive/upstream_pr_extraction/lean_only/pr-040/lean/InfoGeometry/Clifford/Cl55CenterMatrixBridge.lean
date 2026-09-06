import Mathlib
import InfoGeometry.Clifford.Clifford55

namespace InfoGeometry.Clifford.Clifford55

/-!
# Native matrix-center transfer

This is the reusable algebraic step for the `Cl(5,5)` kernel proof.  Once a
faithful full matrix `AlgEquiv` is supplied, central elements are scalar by
Mathlib's native `Matrix.center_eq_range` theorem.
-/

theorem center_scalar_of_algEquiv_matrix
    {R A : Type*}
    [CommRing R] [Semiring A] [Algebra R A]
    {n : Type*} [Fintype n] [DecidableEq n]
    (e : A ≃ₐ[R] Matrix n n R)
    {x : A} (hx : x ∈ Subalgebra.center R A) :
    ∃ r : R, algebraMap R A r = x := by
  have hcenter : e x ∈ Set.center (Matrix n n R) := by
    rw [Set.mem_center_iff]
    refine ⟨?_, ?_, ?_⟩
    · intro y
      obtain ⟨z, rfl⟩ := e.surjective y
      have hz := (Subalgebra.mem_center_iff.mp hx) z
      simpa only [map_mul] using (congrArg e hz).symm
    · intro b c
      simp only [mul_assoc]
    · intro a b
      simp only [mul_assoc]
  have hscalar : e x ∈ Set.range (Matrix.scalar n) := by
    rw [← Matrix.center_eq_range R]
    exact hcenter
  rcases hscalar with ⟨r, hr⟩
  refine ⟨r, e.injective ?_⟩
  calc
    e (algebraMap R A r) = algebraMap R (Matrix n n R) r :=
      e.commutes r
    _ = Matrix.scalar n r := rfl
    _ = e x := hr

end InfoGeometry.Clifford.Clifford55
