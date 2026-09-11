import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-! A kernel-checked `(5,5)` contact carrier core.

The carrier and split bilinear form are kept independent from later
endomorphism and Pin adapters.  This is the stable algebraic base shared by
those downstream owners.
-/

noncomputable section

namespace InfoGeometry.Orthogonal.O55Contact

abbrev Vector55 := InfoGeometry.Algebra.FiniteSpin.Vec10R

def dualIndex : Fin 10 → Fin 10 :=
  ![(8 : Fin 10), 9, 2, 3, 4, 5, 6, 7, 0, 1]

def contactWeight : Fin 10 → ℤ :=
  ![(-1 : ℤ), -1, 0, 0, 0, 0, 0, 0, 1, 1]

def contactWeightR (i : Fin 10) : ℝ := (contactWeight i : ℝ)

@[simp] theorem dualIndex_involutive (i : Fin 10) :
    dualIndex (dualIndex i) = i := by
  fin_cases i <;> rfl

@[simp] theorem contactWeight_dualIndex (i : Fin 10) :
    contactWeight (dualIndex i) = -contactWeight i := by
  fin_cases i <;> rfl

@[simp] theorem contactWeightR_dualIndex (i : Fin 10) :
    contactWeightR (dualIndex i) = -contactWeightR i := by
  simp [contactWeightR]

def splitPairing (x y : Vector55) : ℝ :=
  x 0 * y 8 + x 1 * y 9 + x 8 * y 0 + x 9 * y 1 +
  x 2 * y 2 + x 3 * y 3 + x 4 * y 4 -
  x 5 * y 5 - x 6 * y 6 - x 7 * y 7

@[simp] theorem splitPairing_zero_left (y : Vector55) :
    splitPairing 0 y = 0 := by simp [splitPairing]

@[simp] theorem splitPairing_zero_right (x : Vector55) :
    splitPairing x 0 = 0 := by simp [splitPairing]

@[simp] theorem splitPairing_add_left (x y z : Vector55) :
    splitPairing (x + y) z = splitPairing x z + splitPairing y z := by
  simp [splitPairing]
  ring

@[simp] theorem splitPairing_add_right (x y z : Vector55) :
    splitPairing x (y + z) = splitPairing x y + splitPairing x z := by
  simp [splitPairing]
  ring

@[simp] theorem splitPairing_sub_left (x y z : Vector55) :
    splitPairing (x - y) z = splitPairing x z - splitPairing y z := by
  simp [sub_eq_add_neg, splitPairing]
  ring

@[simp] theorem splitPairing_sub_right (x y z : Vector55) :
    splitPairing x (y - z) = splitPairing x y - splitPairing x z := by
  simp [sub_eq_add_neg, splitPairing]
  ring

@[simp] theorem splitPairing_neg_left (x y : Vector55) :
    splitPairing (-x) y = -splitPairing x y := by
  simp [splitPairing]
  ring

@[simp] theorem splitPairing_neg_right (x y : Vector55) :
    splitPairing x (-y) = -splitPairing x y := by
  simp [splitPairing]
  ring

@[simp] theorem splitPairing_smul_left (c : ℝ) (x y : Vector55) :
    splitPairing (c • x) y = c * splitPairing x y := by
  simp [splitPairing]
  ring

@[simp] theorem splitPairing_smul_right (c : ℝ) (x y : Vector55) :
    splitPairing x (c • y) = c * splitPairing x y := by
  simp [splitPairing]
  ring

theorem splitPairing_comm (x y : Vector55) :
    splitPairing x y = splitPairing y x := by
  simp [splitPairing]
  ring

def coordinateVector (i : Fin 10) : Vector55 :=
  fun j => if j = i then 1 else 0

@[simp] theorem splitPairing_coordinate_right (x : Vector55) (i : Fin 10) :
    splitPairing x (coordinateVector (dualIndex i)) =
      (if i = 5 ∨ i = 6 ∨ i = 7 then -x i else x i) := by
  fin_cases i <;> simp [splitPairing, coordinateVector, dualIndex]

theorem splitPairing_nondegenerate_left (x : Vector55)
    (h : ∀ y, splitPairing x y = 0) : x = 0 := by
  funext i
  have hi := h (coordinateVector (dualIndex i))
  rw [splitPairing_coordinate_right] at hi
  fin_cases i <;> simpa using hi

theorem splitPairing_nondegenerate_right (y : Vector55)
    (h : ∀ x, splitPairing x y = 0) : y = 0 := by
  apply splitPairing_nondegenerate_left y
  intro x
  rw [splitPairing_comm]
  exact h x

theorem vector55_dimension : Fintype.card (Fin 10) = 10 := by
  rfl

end InfoGeometry.Orthogonal.O55Contact
