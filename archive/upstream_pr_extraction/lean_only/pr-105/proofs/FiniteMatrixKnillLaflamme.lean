import Mathlib

noncomputable section

open Matrix Complex

namespace FiniteMatrixKnillLaflamme

abbrev Observable (n : Type*) := Matrix n n ℂ

/-- Orthogonal Projection Condition -/
def IsOrthogonalProjection {n : Type*} [Fintype n] (P : Observable n) : Prop :=
  Pᴴ = P ∧ P * P = P

/-- General Knill-Laflamme Condition -/
def SatisfiesKnillLaflamme {n ι : Type*} [Fintype n] (P : Observable n) (E : ι → Observable n) : Prop :=
  ∃ lambda_val : ι → ι → ℂ, ∀ a b, P * (E a)ᴴ * E b * P = (lambda_val a b) • P

/-- Definition of a Rank-One Projector from a normalized state vector -/
def rankOneProjector {n : Type*} [Fintype n] (ψ : n → ℂ) : Matrix n n ℂ :=
  vecMulVec ψ (star ψ)

/-- Rank-one compression theorem -/
theorem rankOneProjector_compression {n : Type*} [Fintype n] [DecidableEq n]
    (ψ : n → ℂ) (A : Matrix n n ℂ) :
    rankOneProjector ψ * A * rankOneProjector ψ = dotProduct (star ψ) (A *ᵥ ψ) • rankOneProjector ψ := by
  ext i j
  simp only [rankOneProjector, vecMulVec_apply, dotProduct, mul_apply, mulVec, smul_apply, smul_eq_mul, Pi.star_apply]
  calc ∑ k, (∑ l, ψ i * starRingEnd ℂ (ψ l) * A l k) * (ψ k * starRingEnd ℂ (ψ j))
    _ = ∑ k, ∑ l, (ψ i * starRingEnd ℂ (ψ l) * A l k) * (ψ k * starRingEnd ℂ (ψ j)) := by simp_rw [Finset.sum_mul]
    _ = ∑ k, ∑ l, (starRingEnd ℂ (ψ l) * (A l k * ψ k)) * (ψ i * starRingEnd ℂ (ψ j)) := by congr; ext k; congr; ext l; ring
    _ = (∑ k, ∑ l, starRingEnd ℂ (ψ l) * (A l k * ψ k)) * (ψ i * starRingEnd ℂ (ψ j)) := by simp_rw [←Finset.sum_mul]
    _ = (∑ l, starRingEnd ℂ (ψ l) * ∑ k, A l k * ψ k) * (ψ i * starRingEnd ℂ (ψ j)) := by
      congr 1
      rw [Finset.sum_comm]
      simp_rw [←Finset.mul_sum]

/-- Automatic Knill-Laflamme for any rank-one projector (Degenerate Code) -/
theorem rankOneProjector_knillLaflamme {n ι : Type*} [Fintype n] [DecidableEq n]
    (ψ : n → ℂ) (hψ : dotProduct (star ψ) ψ = 1) (E : ι → Matrix n n ℂ) :
    SatisfiesKnillLaflamme (rankOneProjector ψ) E := by
  use fun a b => dotProduct (star ψ) (((E a)ᴴ * E b) *ᵥ ψ)
  intro a b
  have H := rankOneProjector_compression ψ ((E a)ᴴ * E b)
  simp_rw [←Matrix.mul_assoc] at H
  exact H

end FiniteMatrixKnillLaflamme
