/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.MatrixStageProductDensity
import InfoGeometry.Canonical.FiniteMatrixGibbsFunctional

/-! Positivity of the product-density functional on all matrix observables. -/
noncomputable section
namespace InfoGeometry.QuantumContext.MatrixStageProductDensity

open scoped Kronecker ComplexOrder
open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.Canonical.CuntzMatrixTraceTower
open InfoGeometry.Canonical.FiniteMatrixGibbsFunctional

def diagonalWeight (q : Fin 2 → ℝ) : ∀ n, Fin (2 ^ n) → ℝ
  | 0 => fun _ => 1
  | n + 1 => fun i =>
      diagonalWeight q n ((stageIndexEquiv n).symm i).1 *
        (2 * q ((stageIndexEquiv n).symm i).2)

theorem diagonalWeight_nonneg (q : Fin 2 → ℝ) (hq : ∀ i, 0 ≤ q i) :
    ∀ n i, 0 ≤ diagonalWeight q n i := by
  intro n
  induction n with
  | zero => intro i; exact zero_le_one
  | succ n ih =>
      intro i
      exact mul_nonneg (ih _) (mul_nonneg (by norm_num) (hq _))

theorem density_eq_diagonal (q : Fin 2 → ℝ) (n : ℕ) :
    density (fun i => (q i : ℂ)) n =
      Matrix.diagonal (fun i => (diagonalWeight q n i : ℂ)) := by
  induction n with
  | zero => simp [density, diagonalWeight, Matrix.diagonal_one]
  | succ n ih =>
      rw [density, ih, Matrix.diagonal_kronecker_diagonal]
      ext i j
      by_cases hij : i = j
      · subst j
        simp [Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply,
          Matrix.submatrix_apply, diagonalWeight]
      · have hpre : (stageIndexEquiv n).symm i ≠ (stageIndexEquiv n).symm j :=
          fun h => hij ((stageIndexEquiv n).symm.injective h)
        simp [Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply,
          Matrix.submatrix_apply, hij, hpre]

theorem density_posSemidef (q : Fin 2 → ℝ) (hq : ∀ i, 0 ≤ q i) (n : ℕ) :
    (density (fun i => (q i : ℂ)) n).PosSemidef := by
  rw [density_eq_diagonal]
  apply Matrix.PosSemidef.diagonal
  intro i
  exact Complex.zero_le_real.mpr (diagonalWeight_nonneg q hq n i)

theorem density_star (q : Fin 2 → ℝ) (n : ℕ) :
    star (density (fun i => (q i : ℂ)) n) = density (fun i => (q i : ℂ)) n := by
  apply Matrix.IsHermitian.isSelfAdjoint
  rw [density_eq_diagonal, Matrix.isHermitian_diagonal_iff]
  intro i
  simp [IsSelfAdjoint]

theorem density_stage_positive (q : Fin 2 → ℝ) (hq : ∀ i, 0 ≤ q i)
    (n : ℕ) (X : MatrixStage n) :
    0 ≤ (matrixTraceFunctional n
      (star X * X * density (fun i => (q i : ℂ)) n)).re := by
  have h := weightedTrace_nonneg _ (density_posSemidef q hq n) X
  rw [weightedTrace_apply, Matrix.trace_mul_comm] at h
  rw [matrixTraceFunctional_apply]
  have hc : (1 / (2 ^ n : ℂ)) = ((1 / (2 ^ n : ℝ) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hc]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_nonneg (by positivity) h

end InfoGeometry.QuantumContext.MatrixStageProductDensity
end
