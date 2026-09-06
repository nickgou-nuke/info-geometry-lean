import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib
import proofs.PatchRepresentation
import proofs.StructureTensor

open Matrix
open scoped BigOperators

/-!
# D4 Equivariance of the Structure Tensor
-/

/-- 
Action of a linear transformation T on the structure tensor J.
If gradients are transformed by T, the outer products transform as T * J * Tᵀ.
-/
def transformTensor (T J : Patch2x2) : Patch2x2 :=
  T * J * Tᵀ

variable {ι : Type*} [Fintype ι]

/-- Действие на матрица върху вектор-колона -/
def transformGrad (T : Patch2x2) (v : Fin 2 → ℝ) : Fin 2 → ℝ :=
  T.mulVec v

/-- 
Еквивариантност за единично външно произведение: 
(T v)(T v)ᵀ = T (v vᵀ) Tᵀ
-/
theorem outer2_transform (T : Patch2x2) (v : Fin 2 → ℝ) :
    outer2 (transformGrad T v) = transformTensor T (outer2 v) := by
  ext i j
  dsimp [outer2, transformGrad, transformTensor, vecMulVec, mulVec, dotProduct]
  simp only [mul_apply, transpose_apply, Matrix.of_apply]
  calc
    (∑ k, T i k * v k) * (∑ l, T j l * v l)
      = ∑ k, (T i k * v k) * (∑ l, T j l * v l) := by rw [Finset.sum_mul]
    _ = ∑ k, ∑ l, (T i k * v k) * (T j l * v l) := by simp only [Finset.mul_sum]
    _ = ∑ k, ∑ l, T i k * (v k * v l) * T j l := by
      congr 1; ext k; congr 1; ext l; ring
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro l hl
      exact (Finset.sum_mul Finset.univ
        (fun k => T i k * (v k * v l)) (T j l)).symm

/-- 
Основна Теорема за Еквивариантност:
Структурният тензор на трансформираните градиенти е точно 
трансформираният структурен тензор на оригиналните градиенти.
-/
theorem structureTensor_equivariant (T : Patch2x2) (w : ι → ℝ) (grad : ι → Fin 2 → ℝ) :
    structureTensor w (fun p => transformGrad T (grad p)) = 
    transformTensor T (structureTensor w grad) := by
  dsimp [structureTensor]
  simp_rw [outer2_transform]
  dsimp [transformTensor]
  rw [Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Matrix.mul_smul, Matrix.smul_mul]
