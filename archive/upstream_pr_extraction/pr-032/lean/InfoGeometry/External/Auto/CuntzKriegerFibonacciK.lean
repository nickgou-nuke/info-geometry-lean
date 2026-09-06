import Mathlib.Tactic

/-!
# K-theory for the Fibonacci Cuntz--Krieger algebra

For the Fibonacci adjacency matrix

`A = [[1,1],[1,0]]`,

Cuntz--Krieger K-theory is computed by

* `K₀(O_A)` is computed from `I - Aᵀ`;
* `K₁(O_A)` is computed from the zero preimage of `I - Aᵀ`.

Here `I - Aᵀ = [[0,-1],[-1,1]]` has determinant `-1`, hence is unimodular over
`ℤ`.  We prove an explicit integer inverse, then record the computational
consequences: the map on `ℤ²` is surjective and sends only zero to zero, so the
corresponding `K₀` and `K₁` groups are trivial.
-/

noncomputable section

namespace CuntzKriegerFibonacciK

open Matrix

abbrev Z2 := Fin 2 → ℤ
abbrev M2Z := Matrix (Fin 2) (Fin 2) ℤ

/-- Fibonacci adjacency matrix. -/
def A : M2Z := !![1, 1; 1, 0]

/-- Matrix `I - Aᵀ` for Cuntz--Krieger K-theory. -/
def B : M2Z := !![0, -1; -1, 1]

/-- Explicit integer inverse of `B`. -/
def C : M2Z := !![-1, -1; -1, 0]

/-- `B` is indeed `I - Aᵀ`. -/
theorem B_eq_I_sub_AT : B = (1 : M2Z) - Aᵀ := by
  ext i j
  fin_cases i
  all_goals fin_cases j <;> norm_num [B, A]

/-- Determinant of `I - Aᵀ` is `-1`. -/
theorem B_det : B.det = -1 := by
  norm_num [B, Matrix.det_fin_two]

/-- Right inverse over `ℤ`. -/
theorem B_mul_C : B * C = (1 : M2Z) := by
  ext i j
  fin_cases i
  all_goals fin_cases j <;> norm_num [B, C]

/-- Left inverse over `ℤ`. -/
theorem C_mul_B : C * B = (1 : M2Z) := by
  ext i j
  fin_cases i
  all_goals fin_cases j <;> norm_num [B, C]

/-- Matrix-vector action of the Cuntz--Krieger map. -/
def ckMap (v : Z2) : Z2 := B.mulVec v

/-- The Cuntz--Krieger map is surjective. -/
theorem ckMap_surjective : Function.Surjective ckMap := by
  intro v
  use C.mulVec v
  ext i
  fin_cases i <;> simp [ckMap, B, C, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The Cuntz--Krieger map sends only zero to zero. -/
theorem ckMap_eq_zero (v : Z2) (h : ckMap v = 0) : v = 0 := by
  have hleft : C.mulVec (ckMap v) = v := by
    ext i
    fin_cases i <;> simp [ckMap, B, C, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [← hleft, h]
  ext i
  fin_cases i <;> simp [C, Matrix.mulVec, dotProduct]

end CuntzKriegerFibonacciK
