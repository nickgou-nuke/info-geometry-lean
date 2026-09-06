import Mathlib

/-!
# Finite Cuntz--Krieger boundary maps

Repaired external file: compute the integer `2×2` boundary maps `I-Aᵀ` for
Penrose/Fibonacci substitution matrices and prove explicit unimodular inverses.
This is the algebraic input behind trivial cokernel statements; no Morita
classification is asserted here.
-/

noncomputable section

namespace CuntzKriegerKTheory

open Matrix

abbrev M2Z := Matrix (Fin 2) (Fin 2) ℤ

/-- The 2D Penrose rhomb substitution matrix. -/
def PenroseM : M2Z := !![2, 1; 1, 1]

/-- The 1D Fibonacci substitution matrix. -/
def FibonacciF : M2Z := !![1, 1; 1, 0]

/-- Boundary map `I-Mᵀ` for the Penrose matrix. -/
def PenroseMap : M2Z := (1 : M2Z) - PenroseM.transpose

/-- Boundary map `I-Fᵀ` for the Fibonacci matrix. -/
def FibonacciMap : M2Z := (1 : M2Z) - FibonacciF.transpose

/-- Explicit integer inverse of `PenroseMap`. -/
def PenroseMapInv : M2Z := !![0, -1; -1, 1]

/-- Explicit integer inverse of `FibonacciMap`. -/
def FibonacciMapInv : M2Z := !![-1, -1; -1, 0]

theorem penrose_ktheory_det : PenroseMap.det = -1 := by
  simp [PenroseMap, PenroseM, Matrix.det_fin_two]

theorem fibonacci_ktheory_det : FibonacciMap.det = -1 := by
  simp [FibonacciMap, FibonacciF, Matrix.det_fin_two]

/-- `PenroseMap` is unimodular, with an explicit two-sided inverse. -/
theorem penrose_map_unimodular :
    PenroseMap * PenroseMapInv = (1 : M2Z) ∧ PenroseMapInv * PenroseMap = (1 : M2Z) := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [PenroseMap, PenroseMapInv, PenroseM, Matrix.mul_apply, Fin.sum_univ_two]

/-- `FibonacciMap` is unimodular, with an explicit two-sided inverse. -/
theorem fibonacci_map_unimodular :
    FibonacciMap * FibonacciMapInv = (1 : M2Z) ∧ FibonacciMapInv * FibonacciMap = (1 : M2Z) := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [FibonacciMap, FibonacciMapInv, FibonacciF, Matrix.mul_apply, Fin.sum_univ_two]

/-- The two finite boundary maps are both invertible over `ℤ`. -/
theorem cuntz_krieger_boundary_maps_unimodular :
    PenroseMap.det = -1 ∧ FibonacciMap.det = -1 ∧
      PenroseMap * PenroseMapInv = (1 : M2Z) ∧ FibonacciMap * FibonacciMapInv = (1 : M2Z) := by
  exact ⟨penrose_ktheory_det, fibonacci_ktheory_det,
    penrose_map_unimodular.1, fibonacci_map_unimodular.1⟩

#check penrose_ktheory_det
#check fibonacci_ktheory_det
#check penrose_map_unimodular
#check fibonacci_map_unimodular

end CuntzKriegerKTheory
