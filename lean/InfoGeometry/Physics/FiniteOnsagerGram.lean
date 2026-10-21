/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.SuperMetriplectic.Flow
import Mathlib.Tactic

/-!
# Dissipation from a Gram operator, not from an alternating form

For arbitrary real matrices A and R the generator (A-Aᵀ) + RᵀR has
nonnegative quadratic production.  Positivity is derived from R, not assumed.
This is a finite algebraic Onsager identity, not a thermodynamic assertion
about an unspecified evolution or potential. The canonical metriplectic-flow
constructor remains `SuperMetriplectic.matrixMetriplecticFlow`; this file owns
the Gram operator and its positivity facts.
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

open InfoGeometry.SuperMetriplectic

/-- The Gram operator induced by `R`, acting on the finite force space `n → ℝ`.

This is the concrete linear operator represented by `RᵀR`; it is the carrier
level construction that connects the finite matrix dissipation theorem above
to `OnsagerMetricData`. -/
def gramOnsagerLinear (R : Matrix m n ℝ) : (n → ℝ) →ₗ[ℝ] (n → ℝ) :=
  (Matrix.toLin' Rᵀ).comp (Matrix.toLin' R)

/-- A finite Gram matrix gives genuine symmetric, positive Onsager data. -/
def gramOnsagerMetricData (R : Matrix m n ℝ) : OnsagerMetricData (n → ℝ) where
  onsager := gramOnsagerLinear R
  pairing := dotProduct
  metric_symmetric := by
    intro x y
    change dotProduct x ((gramOnsagerLinear R) y) =
      dotProduct y ((gramOnsagerLinear R) x)
    simp only [gramOnsagerLinear, LinearMap.coe_comp, Function.comp_apply,
      Matrix.toLin'_apply]
    rw [dot_transpose_mulVec, dot_transpose_mulVec]
    simp [dotProduct, mul_comm]
  metric_nonnegative := by
    intro x
    change 0 ≤ dotProduct x ((gramOnsagerLinear R) x)
    simp only [gramOnsagerLinear, LinearMap.coe_comp, Function.comp_apply,
      Matrix.toLin'_apply]
    exact gram_contraction_nonnegative R x
  pairing_zero_right := by
    intro x
    simp

theorem gramOnsagerMetricData_quadratic_nonnegative
    (R : Matrix m n ℝ) (x : n → ℝ) :
    0 ≤ (gramOnsagerMetricData R).quadratic x := by
  change 0 ≤ dotProduct x (Rᵀ *ᵥ (R *ᵥ x))
  exact gram_contraction_nonnegative R x

theorem gramOnsagerMetricData_quadratic_eq_zero_iff
    (R : Matrix m n ℝ) (x : n → ℝ) :
    (gramOnsagerMetricData R).quadratic x = 0 ↔ R *ᵥ x = 0 := by
  change dotProduct x (Rᵀ *ᵥ (R *ᵥ x)) = 0 ↔ R *ᵥ x = 0
  exact gram_contraction_eq_zero_iff R x

end InfoGeometry.Physics.FiniteOnsagerGram
