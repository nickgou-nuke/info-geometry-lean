import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib

open Matrix
open scoped BigOperators

abbrev Patch2x2 := Matrix (Fin 2) (Fin 2) ℝ

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

/-- Външно произведение на вектор (колонна по редова матрица) -/
def outer2 (u : Fin 2 → ℝ) : Patch2x2 :=
  vecMulVec u u

/-- Структурният тензор като сума от външни произведения -/
def structureTensor (w : ι → ℝ) (grad : ι → Fin 2 → ℝ) : Patch2x2 :=
  ∑ p, w p • outer2 (grad p)

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
  calc
    (∑ k, T i k * v k) * (∑ l, T j l * v l)
      = ∑ k, (T i k * v k) * (∑ l, T j l * v l) := by rw [Finset.sum_mul]
    _ = ∑ k, ∑ l, (T i k * v k) * (T j l * v l) := by simp only [Finset.mul_sum]
    _ = ∑ k, ∑ l, T i k * (v k * v l) * T j l := by
      congr 1; ext k; congr 1; ext l; ring

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
  -- Matrix multiplication distributes over scalar multiplication and sums
  ext i j
  simp only [mul_apply, smul_apply, Finset.sum_mul, Finset.mul_sum, smul_eq_mul]
  congr 1; ext k
  congr 1; ext l
  ring
