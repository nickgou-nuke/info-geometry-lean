import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Tactic

/-!
# Dissipation from a Gram operator, not from an alternating form

For arbitrary real matrices A and R the generator (A-Aᵀ) + RᵀR has
nonnegative quadratic production.  Positivity is derived from R, not assumed.
This is a finite algebraic Onsager identity, not a thermodynamic assertion
about an unspecified evolution or potential.
-/

namespace InfoGeometry.Physics.FiniteOnsagerGram

open Matrix

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

theorem dot_transpose_mulVec (R : Matrix m n ℝ) (x : n → ℝ) (y : m → ℝ) :
    dotProduct x (Rᵀ *ᵥ y) = dotProduct (R *ᵥ x) y := by
  classical
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The exact quadratic form of the Gram operator. -/
theorem gram_contraction (R : Matrix m n ℝ) (x : n → ℝ) :
    dotProduct x (Rᵀ *ᵥ (R *ᵥ x)) = ∑ i : m, ((R *ᵥ x) i) ^ 2 := by
  rw [dot_transpose_mulVec]
  simp only [dotProduct, pow_two]

theorem gram_contraction_nonnegative (R : Matrix m n ℝ) (x : n → ℝ) :
    0 ≤ dotProduct x (Rᵀ *ᵥ (R *ᵥ x)) := by
  rw [gram_contraction]
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

/-- The reversible skew part contributes no quadratic production. -/
theorem skew_contraction_zero (A : Matrix n n ℝ) (x : n → ℝ) :
    dotProduct x ((A - Aᵀ) *ᵥ x) = 0 := by
  have hsub : (A - Aᵀ) *ᵥ x = A *ᵥ x - Aᵀ *ᵥ x := by
    ext i
    simp [Matrix.mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib]
  rw [hsub]
  have hdot : dotProduct x (A *ᵥ x - Aᵀ *ᵥ x) =
      dotProduct x (A *ᵥ x) - dotProduct x (Aᵀ *ᵥ x) := by
    simp [dotProduct, mul_sub, Finset.sum_sub_distrib]
  rw [hdot, dot_transpose_mulVec]
  simp [dotProduct, mul_comm]

/-- A concrete symmetric-skew generator with production proved nonnegative. -/
theorem onsager_production (A : Matrix n n ℝ) (R : Matrix m n ℝ) (x : n → ℝ) :
    dotProduct x ((A - Aᵀ) *ᵥ x + Rᵀ *ᵥ (R *ᵥ x)) =
      ∑ i : m, ((R *ᵥ x) i) ^ 2 := by
  have hadd : dotProduct x ((A - Aᵀ) *ᵥ x + Rᵀ *ᵥ (R *ᵥ x)) =
      dotProduct x ((A - Aᵀ) *ᵥ x) + dotProduct x (Rᵀ *ᵥ (R *ᵥ x)) := by
    simp [dotProduct, mul_add, Finset.sum_add_distrib]
  rw [hadd, skew_contraction_zero, zero_add, gram_contraction]

theorem onsager_production_nonnegative
    (A : Matrix n n ℝ) (R : Matrix m n ℝ) (x : n → ℝ) :
    0 ≤ dotProduct x ((A - Aᵀ) *ᵥ x + Rᵀ *ᵥ (R *ᵥ x)) := by
  rw [onsager_production]
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

/-- Zero production is precisely the kernel of the chosen dissipative factor. -/
theorem gram_contraction_eq_zero_iff (R : Matrix m n ℝ) (x : n → ℝ) :
    dotProduct x (Rᵀ *ᵥ (R *ᵥ x)) = 0 ↔ R *ᵥ x = 0 := by
  rw [gram_contraction]
  constructor
  · intro h
    funext i
    have hle : ((R *ᵥ x) i) ^ 2 ≤ ∑ j : m, ((R *ᵥ x) j) ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    have hz : ((R *ᵥ x) i) ^ 2 = 0 :=
      le_antisymm (by simpa only [h] using hle) (sq_nonneg _)
    exact sq_eq_zero_iff.mp hz
  · intro h
    simp [h]

end InfoGeometry.Physics.FiniteOnsagerGram
