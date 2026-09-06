import Mathlib

/-!
# Klein geometry as a determinant supergrading

Repaired external file: determinant parity for `2×2` real linear parts, with
multiplicativity and the odd×odd=even rule.
-/

noncomputable section

namespace KleinGeometrySupergraded

open Matrix

abbrev M2R := Matrix (Fin 2) (Fin 2) ℝ

/-- Orientation parity is determinant. -/
def parity (A : M2R) : ℝ := A.det

/-- Identity linear part is even. -/
theorem translation_parity_even : parity (1 : M2R) = 1 := by
  simp [parity]

/-- Reflection across the x-axis. -/
def Rx : M2R := !![1, 0; 0, -1]

/-- Reflection has determinant `-1`. -/
theorem glide_parity_odd : parity Rx = -1 := by
  simp [parity, Rx, Matrix.det_fin_two]

/-- Determinant parity is multiplicative under composition. -/
theorem composition_parity_is_supergraded (A B : M2R) : parity (A * B) = parity A * parity B := by
  simp [parity, Matrix.det_mul]

/-- Odd followed by odd is even. -/
theorem odd_mul_odd_is_even (A B : M2R) (hA : parity A = -1) (hB : parity B = -1) :
    parity (A * B) = 1 := by
  rw [composition_parity_is_supergraded, hA, hB]
  norm_num

#check translation_parity_even
#check glide_parity_odd
#check composition_parity_is_supergraded
#check odd_mul_odd_is_even

end KleinGeometrySupergraded
