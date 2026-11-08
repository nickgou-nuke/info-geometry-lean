/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Fin

/-!
# Projective Upper-Triangular Leakage Matrix (`Su2Su3ProjectiveBridge`)

- BUCKET 1 (Established Mathematical Target & Existing Owners):
  * $3 \times 3$ upper-triangular unipotent matrix `grand_unification_matrix T_leakage`
    over $\mathbb{R}$, together with `unitLeakageMatrix` and `unitLeakageMatrixTranspose`.
- BUCKET 2 (Deconfabulation):
  * Proves both the unipotent square law `(grand_unification_matrix T)^2 = grand_unification_matrix (2*T)`
    and the concrete non-commutativity witness `unitLeakageMatrix * unitLeakageMatrixTranspose ≠ unitLeakageMatrixTranspose * unitLeakageMatrix`.
- BUCKET 3 (Constructive Lean 4 Theorems Proved Here):
  * `sum_fin_3`, `master_symmetry_reconciliation`,
    `grand_unification_matrix_transpose_noncommutative`.
-/

open Matrix

namespace InfoGeometry.GrandUnification.Su2Su3ProjectiveBridge

/-- The $3 \times 3$ upper-triangular unipotent projective leakage matrix over $\mathbb{R}$. -/
def grand_unification_matrix (T_leakage : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  ![![1, 0, 0],
    ![0, 1, T_leakage],
    ![0, 0, 1]]

/-- Unit-leakage specialization `grand_unification_matrix 1`. -/
def unitLeakageMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
  grand_unification_matrix 1

/-- Transpose of `unitLeakageMatrix`. -/
def unitLeakageMatrixTranspose : Matrix (Fin 3) (Fin 3) ℝ :=
  (grand_unification_matrix 1)ᵀ

/-- Explicit three-term expansion of a sum over `Fin 3`. -/
lemma sum_fin_3 {α : Type*} [AddCommMonoid α] (f : Fin 3 → α) :
    ∑ i : Fin 3, f i = f 0 + f 1 + f 2 := by
  rw [Fin.sum_univ_three]

/-- Squaring `grand_unification_matrix T_leakage` doubles the upper-triangular `(1, 2)` shear
entry (`2 * T_leakage`). -/
theorem master_symmetry_reconciliation (T_leakage : ℝ) :
    (grand_unification_matrix T_leakage) * (grand_unification_matrix T_leakage) =
    ![![1, 0, 0], ![0, 1, 2 * T_leakage], ![0, 0, 1]] := by
  ext i j
  fin_cases i
  · fin_cases j
    · rw [mul_apply, sum_fin_3]
      change (1 : ℝ) * 1 + 0 * 0 + 0 * 0 = 1
      norm_num
    · rw [mul_apply, sum_fin_3]
      change (1 : ℝ) * 0 + 0 * 1 + 0 * 0 = 0
      norm_num
    · rw [mul_apply, sum_fin_3]
      change (1 : ℝ) * 0 + 0 * T_leakage + 0 * 1 = 0
      norm_num
  · fin_cases j
    · rw [mul_apply, sum_fin_3]
      change (0 : ℝ) * 1 + 1 * 0 + T_leakage * 0 = 0
      norm_num
    · rw [mul_apply, sum_fin_3]
      change (0 : ℝ) * 0 + 1 * 1 + T_leakage * 0 = 1
      norm_num
    · rw [mul_apply, sum_fin_3]
      change (0 : ℝ) * 0 + 1 * T_leakage + T_leakage * 1 = 2 * T_leakage
      ring
  · fin_cases j
    · rw [mul_apply, sum_fin_3]
      change (0 : ℝ) * 1 + 0 * 0 + 1 * 0 = 0
      norm_num
    · rw [mul_apply, sum_fin_3]
      change (0 : ℝ) * 0 + 0 * 1 + 1 * 0 = 0
      norm_num
    · rw [mul_apply, sum_fin_3]
      change (0 : ℝ) * 0 + 0 * T_leakage + 1 * 1 = 1
      norm_num

/-- Concrete $3 \times 3$ non-commutativity witness: at unit leakage $T = 1$,
`unitLeakageMatrix` does not commute with `unitLeakageMatrixTranspose`. -/
theorem grand_unification_matrix_transpose_noncommutative :
    unitLeakageMatrix * unitLeakageMatrixTranspose ≠
      unitLeakageMatrixTranspose * unitLeakageMatrix := by
  intro h
  have h11 :
      (unitLeakageMatrix * unitLeakageMatrixTranspose) 1 1 =
        (unitLeakageMatrixTranspose * unitLeakageMatrix) 1 1 :=
    congrFun (congrFun h 1) 1
  dsimp [unitLeakageMatrix, unitLeakageMatrixTranspose] at h11
  rw [mul_apply, mul_apply, sum_fin_3, sum_fin_3] at h11
  change (0 : ℝ) * 0 + 1 * 1 + 1 * 1 = 0 * 0 + 1 * 1 + 0 * 0 at h11
  norm_num at h11

end InfoGeometry.GrandUnification.Su2Su3ProjectiveBridge
