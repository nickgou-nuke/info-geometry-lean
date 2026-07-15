import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.FinCases
import InfoGeometry.Canonical.ZornVectorMatrixExplicit

namespace InfoGeometry.Physics.ZornMatrixSU3

/-!
## 1. Vector Cross Product in ℝ³
-/

/-- Cross product in ℝ³ -/
def crossProduct (x y : Fin 3 → ℝ) : Fin 3 → ℝ := ZornVectorMatrixExplicit.cross3 x y

/-- Dot product in ℝ³ -/
def dotProduct (x y : Fin 3 → ℝ) : ℝ := ZornVectorMatrixExplicit.dot3 x y

theorem dotProduct_comm (x y : Fin 3 → ℝ) :
    dotProduct x y = dotProduct y x := by
  simpa [dotProduct] using
    ZornVectorMatrixExplicit.dot3_comm x y

@[simp] theorem dotProduct_zero_left (x : Fin 3 → ℝ) :
    dotProduct (fun _ : Fin 3 => 0) x = 0 := by
  simp [dotProduct, ZornVectorMatrixExplicit.dot3]

@[simp] theorem dotProduct_zero_right (x : Fin 3 → ℝ) :
    dotProduct x (fun _ : Fin 3 => 0) = 0 := by
  simpa [dotProduct_comm] using dotProduct_zero_left x

@[simp] theorem dotProduct_zero_zero :
    dotProduct (0 : Fin 3 → ℝ) (0 : Fin 3 → ℝ) = 0 := by
  simp [dotProduct, ZornVectorMatrixExplicit.dot3]

theorem dotProduct_add_left (x y z : Fin 3 → ℝ) :
    dotProduct (x + y) z = dotProduct x z + dotProduct y z := by
  simp [dotProduct, ZornVectorMatrixExplicit.dot3]
  ring

theorem dotProduct_add_right (x y z : Fin 3 → ℝ) :
    dotProduct x (y + z) = dotProduct x y + dotProduct x z := by
  simp [dotProduct, ZornVectorMatrixExplicit.dot3]
  ring

theorem dotProduct_smul_left (r : ℝ) (x y : Fin 3 → ℝ) :
    dotProduct (r • x) y = r * dotProduct x y := by
  simp [dotProduct, ZornVectorMatrixExplicit.dot3]
  ring

theorem dotProduct_smul_right (r : ℝ) (x y : Fin 3 → ℝ) :
    dotProduct x (r • y) = r * dotProduct x y := by
  simp [dotProduct, ZornVectorMatrixExplicit.dot3]
  ring

@[simp] theorem crossProduct_zero_left (x : Fin 3 → ℝ) :
    crossProduct (fun _ : Fin 3 => 0) x = (0 : Fin 3 → ℝ) := by
  funext i
  fin_cases i <;> simp [crossProduct, ZornVectorMatrixExplicit.cross3]

@[simp] theorem crossProduct_zero_zero :
    crossProduct (0 : Fin 3 → ℝ) (0 : Fin 3 → ℝ) = (0 : Fin 3 → ℝ) := by
  funext i
  fin_cases i <;> simp [crossProduct, ZornVectorMatrixExplicit.cross3]

@[simp] theorem crossProduct_zero_right (x : Fin 3 → ℝ) :
    crossProduct x (fun _ : Fin 3 => 0) = (0 : Fin 3 → ℝ) := by
  funext i
  fin_cases i <;> simp [crossProduct, ZornVectorMatrixExplicit.cross3]

theorem crossProduct_add_left (x y z : Fin 3 → ℝ) :
    crossProduct (x + y) z = crossProduct x z + crossProduct y z := by
  funext i
  fin_cases i <;>
    simp [crossProduct, ZornVectorMatrixExplicit.cross3] <;>
    ring

theorem crossProduct_add_right (x y z : Fin 3 → ℝ) :
    crossProduct x (y + z) = crossProduct x y + crossProduct x z := by
  funext i
  fin_cases i <;>
    simp [crossProduct, ZornVectorMatrixExplicit.cross3] <;>
    ring

theorem crossProduct_smul_left (r : ℝ) (x y : Fin 3 → ℝ) :
    crossProduct (r • x) y = r • crossProduct x y := by
  funext i
  fin_cases i <;>
    simp [crossProduct, ZornVectorMatrixExplicit.cross3] <;>
    ring

theorem crossProduct_smul_right (r : ℝ) (x y : Fin 3 → ℝ) :
    crossProduct x (r • y) = r • crossProduct x y := by
  funext i
  fin_cases i <;>
    simp [crossProduct, ZornVectorMatrixExplicit.cross3] <;>
    ring

theorem crossProduct_anticomm (x y : Fin 3 → ℝ) :
    crossProduct x y = -(crossProduct y x) := by
  ext i
  fin_cases i <;> simp [crossProduct, ZornVectorMatrixExplicit.cross3] <;> ring

@[simp] theorem crossProduct_self (x : Fin 3 → ℝ) :
    crossProduct x x = (0 : Fin 3 → ℝ) := by
  ext i
  fin_cases i <;> simp [crossProduct, ZornVectorMatrixExplicit.cross3] <;> ring

theorem dotProduct_crossProduct_left (x y : Fin 3 → ℝ) :
    dotProduct x (crossProduct x y) = 0 := by
  simp [dotProduct, crossProduct, ZornVectorMatrixExplicit.dot3,
    ZornVectorMatrixExplicit.cross3, Fin.sum_univ_three]
  ring_nf

theorem dotProduct_crossProduct_right (x y : Fin 3 → ℝ) :
    dotProduct y (crossProduct x y) = 0 := by
  simp [dotProduct, crossProduct, ZornVectorMatrixExplicit.dot3,
    ZornVectorMatrixExplicit.cross3, Fin.sum_univ_three]
  ring_nf

theorem crossProduct_triple (x y z : Fin 3 → ℝ) :
    crossProduct x (crossProduct y z) =
      dotProduct x z • y - dotProduct x y • z := by
  ext i <;> fin_cases i <;>
    simp [dotProduct, crossProduct, ZornVectorMatrixExplicit.dot3,
      ZornVectorMatrixExplicit.cross3, Fin.sum_univ_three] <;>
    ring_nf

end InfoGeometry.Physics.ZornMatrixSU3
