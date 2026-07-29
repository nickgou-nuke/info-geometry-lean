import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Ring.Basic

namespace CuntzAlgebra

variable {A : Type*} [Ring A] [StarRing A]

/-- The pair of generators S₁, S₂ for the Cuntz algebra 𝒪₂.
    They are isometries (Sᵢ* Sᵢ = 1) whose range projections sum to 1. -/
structure Cuntz2Isometries (A : Type*) [Ring A] [StarRing A] where
  S1 : A
  S2 : A
  h_isometry1 : star S1 * S1 = 1
  h_isometry2 : star S2 * S2 = 1
  h_range_sum : S1 * star S1 + S2 * star S2 = 1

/-- Range projection P₁ = S₁ S₁* -/
def rangeProj1 (c : Cuntz2Isometries A) : A :=
  c.S1 * star c.S1

/-- Range projection P₂ = S₂ S₂* -/
def rangeProj2 (c : Cuntz2Isometries A) : A :=
  c.S2 * star c.S2

/-- 🏆 THEOREM 1: Range projection P₁ is idempotent (P₁² = P₁) -/
theorem rangeProj1_idem (c : Cuntz2Isometries A) :
    rangeProj1 c * rangeProj1 c = rangeProj1 c := by
  dsimp [rangeProj1]
  rw [mul_assoc c.S1 (star c.S1) (c.S1 * star c.S1)]
  rw [← mul_assoc (star c.S1) c.S1 (star c.S1)]
  rw [c.h_isometry1, one_mul]

/-- 🏆 THEOREM 2: Range projection P₂ is idempotent (P₂² = P₂) -/
theorem rangeProj2_idem (c : Cuntz2Isometries A) :
    rangeProj2 c * rangeProj2 c = rangeProj2 c := by
  dsimp [rangeProj2]
  rw [mul_assoc c.S2 (star c.S2) (c.S2 * star c.S2)]
  rw [← mul_assoc (star c.S2) c.S2 (star c.S2)]
  rw [c.h_isometry2, one_mul]

/-- 🏆 THEOREM 3: Orthogonality of Isometries S₁* S₂ = 0 -/
theorem isometries_ortho (c : Cuntz2Isometries A) :
    star c.S1 * c.S2 = 0 := by
  have h : star c.S1 * c.S2 = star c.S1 * c.S2 + star c.S1 * c.S2 := by
    calc star c.S1 * c.S2
      _ = star c.S1 * (1 * c.S2) := by rw [one_mul]
      _ = star c.S1 * ((c.S1 * star c.S1 + c.S2 * star c.S2) * c.S2) := by rw [c.h_range_sum]
      _ = star c.S1 * (c.S1 * star c.S1 * c.S2 + c.S2 * star c.S2 * c.S2) := by rw [add_mul]
      _ = star c.S1 * (c.S1 * star c.S1 * c.S2) + star c.S1 * (c.S2 * star c.S2 * c.S2) := by rw [mul_add]
      _ = (star c.S1 * c.S1) * (star c.S1 * c.S2) + (star c.S1 * c.S2) * (star c.S2 * c.S2) := by simp [mul_assoc]
      _ = 1 * (star c.S1 * c.S2) + (star c.S1 * c.S2) * 1 := by rw [c.h_isometry1, c.h_isometry2]
      _ = star c.S1 * c.S2 + star c.S1 * c.S2 := by rw [one_mul, mul_one]
  have h2 : star c.S1 * c.S2 + 0 = star c.S1 * c.S2 + star c.S1 * c.S2 := by
    rw [add_zero]
    exact h
  exact (add_left_cancel h2).symm

/-- 🏆 THEOREM 4: Orthogonality of Range Projections P₁ P₂ = 0 -/
theorem rangeProjs_ortho (c : Cuntz2Isometries A) :
    rangeProj1 c * rangeProj2 c = 0 := by
  dsimp [rangeProj1, rangeProj2]
  rw [mul_assoc c.S1 (star c.S1) (c.S2 * star c.S2)]
  rw [← mul_assoc (star c.S1) c.S2 (star c.S2)]
  rw [isometries_ortho c, zero_mul, mul_zero]

end CuntzAlgebra
