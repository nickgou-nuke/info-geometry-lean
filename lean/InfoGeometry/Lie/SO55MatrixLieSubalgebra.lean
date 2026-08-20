import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Tactic
import InfoGeometry.Lie.SplitOctonionSO44SO55OrthogonalBridge

/-!
# The $\mathfrak{so}(5,5)$ Matrix Lie Subalgebra

This module constructs the exact 45-dimensional matrix Lie subalgebra:
  `so55LieSubalgebra : LieSubalgebra ℝ Mat10`
defined by the split signature condition:
  `Mᵀ * eta55 + eta55 * M = 0`

All Lie algebraic closure properties:
1. `isSO55_zero`
2. `isSO55_add`
3. `isSO55_smul`
4. `isSO55_bracket`
are mechanically verified in Lean 4 with ZERO `sorry`s and ZERO custom axioms.
-/

noncomputable section

namespace InfoGeometry.Lie.SO55MatrixSubalgebra

open Matrix

abbrev Mat10 := Matrix (Fin 10) (Fin 10) ℝ

/-- The split-signature metric in the Levi/Witt basis used by the derivation map. -/
abbrev eta55 : Mat10 :=
  InfoGeometry.Lie.SplitOctonionSO44SO55OrthogonalBridge.eta55LeviMat10

/-- $\eta_{5,5}$ is symmetric: $\eta_{5,5}^T = \eta_{5,5}$. -/
theorem eta55_transpose : eta55ᵀ = eta55 := by
  ext i j
  dsimp [eta55]
  by_cases hij : i = j
  · subst hij; simp
  · have hji : ¬ j = i := fun h => hij h.symm
    simp [hij, hji]

/-- Condition for a 10x10 matrix to be skew-adjoint with respect to $\eta_{5,5}$. -/
def IsSO55Matrix (M : Mat10) : Prop :=
  Mᵀ * eta55 + eta55 * M = 0

theorem isSO55_zero : IsSO55Matrix (0 : Mat10) := by
  dsimp [IsSO55Matrix]
  simp

theorem isSO55_add {M N : Mat10} (hM : IsSO55Matrix M) (hN : IsSO55Matrix N) :
    IsSO55Matrix (M + N) := by
  dsimp [IsSO55Matrix] at *
  calc (M + N)ᵀ * eta55 + eta55 * (M + N)
    _ = (Mᵀ + Nᵀ) * eta55 + (eta55 * M + eta55 * N) := by rw [transpose_add, mul_add]
    _ = (Mᵀ * eta55 + eta55 * M) + (Nᵀ * eta55 + eta55 * N) := by
      rw [add_mul]
      abel
    _ = 0 + 0 := by rw [hM, hN]
    _ = 0 := add_zero 0

theorem isSO55_smul (c : ℝ) {M : Mat10} (hM : IsSO55Matrix M) :
    IsSO55Matrix (c • M) := by
  dsimp [IsSO55Matrix] at *
  calc (c • M)ᵀ * eta55 + eta55 * (c • M)
    _ = c • (Mᵀ * eta55) + c • (eta55 * M) := by rw [transpose_smul, smul_mul, Matrix.mul_smul]
    _ = c • (Mᵀ * eta55 + eta55 * M) := by rw [smul_add]
    _ = c • (0 : Mat10) := by rw [hM]
    _ = 0 := smul_zero c

theorem isSO55_bracket {M N : Mat10} (hM : IsSO55Matrix M) (hN : IsSO55Matrix N) :
    IsSO55Matrix (⁅M, N⁆ : Mat10) := by
  dsimp [IsSO55Matrix] at *
  have hM_eq : Mᵀ * eta55 = - (eta55 * M) := eq_neg_of_add_eq_zero_left hM
  have hN_eq : Nᵀ * eta55 = - (eta55 * N) := eq_neg_of_add_eq_zero_left hN
  change (M * N - N * M)ᵀ * eta55 + eta55 * (M * N - N * M) = 0
  rw [transpose_sub, transpose_mul, transpose_mul, sub_mul]
  rw [mul_assoc, mul_assoc]
  rw [hM_eq, hN_eq]
  rw [mul_neg, mul_neg]
  rw [← mul_assoc, ← mul_assoc]
  rw [hN_eq, hM_eq]
  rw [neg_mul, neg_mul, neg_neg, neg_neg]
  rw [mul_sub, mul_assoc, mul_assoc]
  abel

/-- The genuine Lie subalgebra $\mathfrak{so}(5,5)$ inside `Mat10`. -/
def so55LieSubalgebra : LieSubalgebra ℝ Mat10 where
  carrier := { M : Mat10 | IsSO55Matrix M }
  add_mem' {M N} hM hN := isSO55_add hM hN
  zero_mem' := isSO55_zero
  smul_mem' c {M} hM := isSO55_smul c hM
  lie_mem' {M N} hM hN := isSO55_bracket hM hN

end InfoGeometry.Lie.SO55MatrixSubalgebra
