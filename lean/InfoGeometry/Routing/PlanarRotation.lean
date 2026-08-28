import Mathlib

namespace InfoGeometry.Routing.PlanarRotation

noncomputable section

abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℝ

def rotation (φ : ℝ) : Mat2 :=
  !![Real.cos φ, -Real.sin φ; Real.sin φ, Real.cos φ]

def ellipticGenerator : Mat2 := !![0, -1; 1, 0]

theorem ellipticGenerator_sq :
    ellipticGenerator * ellipticGenerator = -(1 : Mat2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ellipticGenerator, Matrix.mul_apply]

theorem rotation_as_elliptic_generator (φ : ℝ) :
    rotation φ = Real.cos φ • (1 : Mat2) + Real.sin φ • ellipticGenerator := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotation, ellipticGenerator]

theorem rotation_zero : rotation 0 = (1 : Mat2) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotation]

theorem rotation_mul_rotation (α β : ℝ) :
    rotation α * rotation β = rotation (α + β) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotation, Matrix.mul_apply, Real.sin_add, Real.cos_add] <;> ring

theorem rotation_mul_neg_rotation (φ : ℝ) :
    rotation φ * rotation (-φ) = (1 : Mat2) := by
  rw [rotation_mul_rotation, add_neg_cancel, rotation_zero]

theorem rotation_transpose (φ : ℝ) :
    Matrix.transpose (rotation φ) = rotation (-φ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotation, Matrix.transpose_apply, Real.sin_neg]

theorem rotation_transpose_mul_self (φ : ℝ) :
    Matrix.transpose (rotation φ) * rotation φ = (1 : Mat2) := by
  rw [rotation_transpose, rotation_mul_rotation, neg_add_cancel, rotation_zero]

def splitRotation (t : ℝ) : Mat2 :=
  !![Real.cosh t, Real.sinh t; Real.sinh t, Real.cosh t]

theorem splitRotation_zero : splitRotation 0 = (1 : Mat2) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [splitRotation]

theorem splitRotation_mul_splitRotation (s t : ℝ) :
    splitRotation s * splitRotation t = splitRotation (s + t) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [splitRotation, Matrix.mul_apply, Real.sinh_add, Real.cosh_add] <;> ring

theorem splitRotation_mul_neg_splitRotation (t : ℝ) :
    splitRotation t * splitRotation (-t) = (1 : Mat2) := by
  rw [splitRotation_mul_splitRotation, add_neg_cancel, splitRotation_zero]

theorem splitRotation_transpose (t : ℝ) :
    Matrix.transpose (splitRotation t) = splitRotation t := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

def splitMetric : Mat2 := !![1, 0; 0, -1]

theorem splitRotation_preserves_metric (t : ℝ) :
    Matrix.transpose (splitRotation t) * splitMetric * splitRotation t =
      splitMetric := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [splitRotation, splitMetric, Matrix.mul_apply,
      Matrix.transpose_apply] <;>
    nlinarith [Real.cosh_sq_sub_sinh_sq t]

theorem splitRotation_det (t : ℝ) :
    Matrix.det (splitRotation t) = 1 := by
  simp [splitRotation, Matrix.det_fin_two]
  nlinarith [Real.cosh_sq_sub_sinh_sq t]

end
end InfoGeometry.Routing.PlanarRotation
