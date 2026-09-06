import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

namespace InfoGeometry.Geometry

abbrev ComplexMat2 := Matrix (Fin 2) (Fin 2) ℂ

structure sl2C where
  a : ℂ
  b : ℂ
  c : ℂ

namespace sl2C

/-- The trace-zero matrix [[a,b],[c,-a]]. -/
def matrix (M : sl2C) : ComplexMat2 :=
  !![M.a, M.b; M.c, -M.a]

/-- The quadratic infinitesimal vector field induced by the trace-zero matrix. -/
def vectorField (M : sl2C) (z : ℂ) : ℂ :=
  -M.c * z ^ 2 + (2 : ℂ) * M.a * z + M.b

/-- The quadratic discriminant of the infinitesimal vector field. -/
def discriminant (M : sl2C) : ℂ :=
  (2 : ℂ) ^ 2 * M.a ^ 2 + (4 : ℂ) * M.b * M.c

@[simp] theorem matrix_00 (M : sl2C) : M.matrix 0 0 = M.a := by rfl
@[simp] theorem matrix_01 (M : sl2C) : M.matrix 0 1 = M.b := by rfl
@[simp] theorem matrix_10 (M : sl2C) : M.matrix 1 0 = M.c := by rfl
@[simp] theorem matrix_11 (M : sl2C) : M.matrix 1 1 = -M.a := by rfl

@[simp] theorem matrix_trace_zero (M : sl2C) : M.matrix 0 0 + M.matrix 1 1 = 0 := by
  simp [matrix]

theorem matrix_det (M : sl2C) : M.matrix.det = -(M.a ^ 2 + M.b * M.c) := by
  simp [matrix, Matrix.det_fin_two]
  ring

theorem discriminant_eq_four_mul (M : sl2C) :
    M.discriminant = (4 : ℂ) * (M.a ^ 2 + M.b * M.c) := by
  simp [discriminant]
  ring

theorem discriminant_eq_neg_four_det (M : sl2C) :
    M.discriminant = (-4 : ℂ) * M.matrix.det := by
  rw [matrix_det, discriminant_eq_four_mul]
  ring

/-- Parabolic sample: repeated root because the discriminant vanishes. -/
def parabolic : sl2C := ⟨1, 1, -1⟩

/-- Hyperbolic sample: real positive discriminant. -/
def hyperbolic : sl2C := ⟨1, 0, -1⟩

/-- Elliptic sample: real negative discriminant. -/
def elliptic : sl2C := ⟨0, 1, -1⟩

/-- Loxodromic sample: non-real discriminant. -/
def loxodromic : sl2C := ⟨1, 1, Complex.I⟩

theorem parabolic_vectorField (z : ℂ) :
    parabolic.vectorField z = z ^ 2 + 2 * z + 1 := by
  simp [parabolic, vectorField]

theorem hyperbolic_vectorField (z : ℂ) :
    hyperbolic.vectorField z = z ^ 2 + 2 * z := by
  simp [hyperbolic, vectorField]

theorem elliptic_vectorField (z : ℂ) :
    elliptic.vectorField z = z ^ 2 + 1 := by
  simp [elliptic, vectorField]

theorem parabolic_discriminant : parabolic.discriminant = 0 := by
  norm_num [parabolic, discriminant]

theorem hyperbolic_discriminant : hyperbolic.discriminant = 4 := by
  norm_num [hyperbolic, discriminant]

theorem elliptic_discriminant : elliptic.discriminant = -4 := by
  norm_num [elliptic, discriminant]

theorem loxodromic_discriminant : loxodromic.discriminant = 4 + 4 * Complex.I := by
  simp [loxodromic, discriminant]
  ring_nf

theorem loxodromic_discriminant_im_ne_zero : loxodromic.discriminant.im ≠ 0 := by
  norm_num [loxodromic_discriminant]

end sl2C

end InfoGeometry.Geometry
