import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CuntzMatrixTowerInstantiation

open Matrix
open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation

noncomputable section

namespace InfoGeometry.Canonical.ConcreteCuntzMatrixIsometries

/-!
# Concrete rectangular isometry frame

This module records explicit 2×1 complex matrix operators $S_1, S_2$ mapping
$\mathbb{C}^1 \to \mathbb{C}^2$:
  $$S_1 = \begin{pmatrix} 1 \\ 0 \end{pmatrix}, \quad S_2 = \begin{pmatrix} 0 \\ 1 \end{pmatrix}$$

They form a finite Parseval frame: each map is an isometry, their ranges are
orthogonal, and the range projections sum to the identity on $\mathbb{C}^2$.
Because these are rectangular maps rather than two elements of one unital
matrix algebra, this file is not a concrete Cuntz-$\mathcal O_2$ realization.

Proved Theorems:
1. $S_1^* S_1 = I_1$ (Isometry)
2. $S_2^* S_2 = I_1$ (Isometry)
3. $S_1^* S_2 = 0$ and $S_2^* S_1 = 0$ (Orthogonality)
4. $P_1 = S_1 S_1^* = \begin{pmatrix} 1 & 0 \\ 0 & 0 \end{pmatrix}$ and $P_2 = S_2 S_2^* = \begin{pmatrix} 0 & 0 \\ 0 & 1 \end{pmatrix}$
5. $S_1 S_1^* + S_2 S_2^* = I_2$ (Completeness relation)
-/

/-- First rectangular isometry as a 2×1 matrix. -/
def cuntzMatrixS1 : Matrix (Fin 2) (Fin 1) ℂ :=
  !![1; 0]

/-- Second rectangular isometry as a 2×1 matrix. -/
def cuntzMatrixS2 : Matrix (Fin 2) (Fin 1) ℂ :=
  !![0; 1]

/-- **Theorem**: The first frame vector is an isometry. -/
theorem cuntzMatrixS1_isometry :
    cuntzMatrixS1.conjTranspose * cuntzMatrixS1 = 1 := by
  ext i j
  fin_cases i
  fin_cases j
  simp [cuntzMatrixS1, conjTranspose_apply, mul_apply, Fin.sum_univ_two]

/-- **Theorem**: The second frame vector is an isometry. -/
theorem cuntzMatrixS2_isometry :
    cuntzMatrixS2.conjTranspose * cuntzMatrixS2 = 1 := by
  ext i j
  fin_cases i
  fin_cases j
  simp [cuntzMatrixS2, conjTranspose_apply, mul_apply, Fin.sum_univ_two]

/-- **Theorem**: Projection P₁ = S₁ S₁* = [1 0; 0 0]. -/
theorem cuntzMatrix_projector1 :
    cuntzMatrixS1 * cuntzMatrixS1.conjTranspose = !![1, 0; 0, 0] := by
  dsimp [cuntzMatrixS1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply, conjTranspose_apply]

/-- **Theorem**: Projection P₂ = S₂ S₂* = [0 0; 0 1]. -/
theorem cuntzMatrix_projector2 :
    cuntzMatrixS2 * cuntzMatrixS2.conjTranspose = !![0, 0; 0, 1] := by
  dsimp [cuntzMatrixS2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply, conjTranspose_apply]

/-- **Theorem**: Completeness Relation S₁ S₁* + S₂ S₂* = 1 (2×2 identity matrix). -/
theorem cuntzMatrix_completeness :
    cuntzMatrixS1 * cuntzMatrixS1.conjTranspose + cuntzMatrixS2 * cuntzMatrixS2.conjTranspose = 1 := by
  rw [cuntzMatrix_projector1, cuntzMatrix_projector2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [add_apply]

/-- **Theorem**: Orthogonality S₁* S₂ = 0 (1×1 zero matrix). -/
theorem cuntzMatrix_orthogonality1 :
    cuntzMatrixS1.conjTranspose * cuntzMatrixS2 = 0 := by
  ext i j
  fin_cases i
  fin_cases j
  simp [cuntzMatrixS1, cuntzMatrixS2, conjTranspose_apply, mul_apply, Fin.sum_univ_two]

/-- **Theorem**: Orthogonality S₂* S₁ = 0 (1×1 zero matrix). -/
theorem cuntzMatrix_orthogonality2 :
    cuntzMatrixS2.conjTranspose * cuntzMatrixS1 = 0 := by
  ext i j
  fin_cases i
  fin_cases j
  simp [cuntzMatrixS1, cuntzMatrixS2, conjTranspose_apply, mul_apply, Fin.sum_univ_two]

end InfoGeometry.Canonical.ConcreteCuntzMatrixIsometries
