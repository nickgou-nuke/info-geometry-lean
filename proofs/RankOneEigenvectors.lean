import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib

open Matrix
open scoped BigOperators

abbrev Patch2x2 := Matrix (Fin 2) (Fin 2) ℝ

/-!
# Subpixel Contours and Eigenvectors of Rank-1 Tensors

This module formally proves the eigensystem properties of a rank-1 
structure tensor J = v vᵀ. It proves that the gradient direction (v) 
is the dominant eigenvector, while the contour tangent (orthogonal to v) 
strictly lies in the null space (kernel) of J.
-/

/-- Външно произведение (J = v vᵀ), представляващо ранг-1 структурен тензор -/
def outer2 (u : Fin 2 → ℝ) : Patch2x2 :=
  vecMulVec u u

/-- 
Теорема 1: Доминантен собствен вектор.
Ако J = v vᵀ е структурен тензор на идеален 1D контур, то градиентният вектор v 
е собствен вектор със собствена стойност ||v||² (vᵀ v). 
Това математически обосновава извличането на градиентната посока от матрицата.
-/
theorem rank_one_eigenvector (v : Fin 2 → ℝ) :
    (outer2 v).mulVec v = (dotProduct v v) • v := by
  ext i
  dsimp [outer2, vecMulVec, mulVec, dotProduct]
  calc
    ∑ j, (v i * v j) * v j 
      = ∑ j, v i * (v j * v j) := by congr 1; ext j; ring
    _ = v i * ∑ j, v j * v j := by rw [Finset.mul_sum]

/-- 
Теорема 2: Тангенциалният контур лежи в нулевото пространство.
Всеки вектор u, който е ортогонален на градиента v (т.е. лежи по дължината на ръба), 
има собствена стойност 0 (принадлежи към ядрото на J). 
Това е основата за анизотропната дифузия, която филтрира само по ядрото!
-/
theorem contour_tangent_in_kernel (v u : Fin 2 → ℝ) (h_ortho : dotProduct v u = 0) :
    (outer2 v).mulVec u = 0 := by
  ext i
  dsimp [outer2, vecMulVec, mulVec]
  calc
    ∑ j, (v i * v j) * u j 
      = ∑ j, v i * (v j * u j) := by congr 1; ext j; ring
    _ = v i * ∑ j, v j * u j := by rw [Finset.mul_sum]
    _ = v i * dotProduct v u := rfl
    _ = v i * 0 := by rw [h_ortho]
    _ = 0 := by ring
