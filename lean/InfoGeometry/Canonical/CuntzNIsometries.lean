import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.BigOperators.Intervals

open BigOperators

namespace CuntzAlgebra

variable {n : ℕ} {A : Type*} [Ring A] [StarRing A]

/-- The generators Sᵢ (i ∈ Fin n) for the general Cuntz algebra 𝒪ₙ.
    They are mutually orthogonal isometries whose range projections sum to 1. -/
structure CuntzIsometries (n : ℕ) (A : Type*) [Ring A] [StarRing A] where
  S : Fin n → A
  h_ortho : ∀ i j : Fin n, i ≠ j → star (S i) * S j = 0
  h_isometry : ∀ i : Fin n, star (S i) * S i = 1
  h_range_sum : ∑ i : Fin n, S i * star (S i) = 1

/-- Range projection Pᵢ = Sᵢ Sᵢ* for generator i -/
def rangeProj (c : CuntzIsometries n A) (i : Fin n) : A :=
  c.S i * star (c.S i)

/-- 🏆 THEOREM 1: Every range projection Pᵢ is idempotent (Pᵢ² = Pᵢ) -/
theorem rangeProj_idem (c : CuntzIsometries n A) (i : Fin n) :
    rangeProj c i * rangeProj c i = rangeProj c i := by
  dsimp [rangeProj]
  rw [mul_assoc (c.S i) (star (c.S i)) (c.S i * star (c.S i))]
  rw [← mul_assoc (star (c.S i)) (c.S i) (star (c.S i))]
  rw [c.h_isometry i, one_mul]

/-- 🏆 THEOREM 2: Distinct range projections are mutually orthogonal (Pᵢ Pⱼ = 0 for i ≠ j) -/
theorem rangeProj_ortho (c : CuntzIsometries n A) {i j : Fin n} (h : i ≠ j) :
    rangeProj c i * rangeProj c j = 0 := by
  dsimp [rangeProj]
  rw [mul_assoc (c.S i) (star (c.S i)) (c.S j * star (c.S j))]
  rw [← mul_assoc (star (c.S i)) (c.S j) (star (c.S j))]
  rw [c.h_ortho i j h, zero_mul, mul_zero]

/-- 🏆 THEOREM 3: Kronecker delta relation Sᵢ* Sⱼ = δᵢⱼ 1 -/
theorem isometry_delta (c : CuntzIsometries n A) (i j : Fin n) :
    star (c.S i) * c.S j = if i = j then 1 else 0 := by
  split_ifs with h
  · subst h
    exact c.h_isometry i
  · exact c.h_ortho i j h

/-- 🏆 THEOREM 4: Partition of Unity - The sum of all range projections equals 1 -/
theorem rangeProj_sum (c : CuntzIsometries n A) :
    ∑ i : Fin n, rangeProj c i = 1 := by
  exact c.h_range_sum

end CuntzAlgebra
