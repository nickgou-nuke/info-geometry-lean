import Mathlib

namespace InfoGeometry.Routing.PlanarRotation

noncomputable section

abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℝ

def rotation (φ : ℝ) : Mat2 :=
  !![Real.cos φ, -Real.sin φ; Real.sin φ, Real.cos φ]

theorem rotation_zero : rotation 0 = (1 : Mat2) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotation]

theorem rotation_mul_rotation (α β : ℝ) :
    rotation α * rotation β = rotation (α + β) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotation, Matrix.mul_apply, Real.sin_add, Real.cos_add] <;> ring

end
end InfoGeometry.Routing.PlanarRotation
