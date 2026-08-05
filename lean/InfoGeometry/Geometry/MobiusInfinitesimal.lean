import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

namespace InfoGeometry.Geometry

abbrev ComplexMat2 := Matrix (Fin 2) (Fin 2) ℂ

/-!
`sl2C` is represented by the native trace-zero matrix subtype.  The
coordinate functions below are readouts, not primitive structure fields.
-/
abbrev sl2C := {M : ComplexMat2 // Matrix.trace M = 0}

namespace sl2C

/-- The trace-zero matrix [[a,b],[c,-a]]. -/
abbrev a (M : sl2C) : ℂ := M.1 0 0

abbrev b (M : sl2C) : ℂ := M.1 0 1

abbrev c (M : sl2C) : ℂ := M.1 1 0

abbrev matrix (M : sl2C) : ComplexMat2 := M.1

def ofCoords (a b c : ℂ) : sl2C :=
  ⟨!![a, b; c, -a], by
    simp [Matrix.trace]
  ⟩

/-- The quadratic infinitesimal vector field induced by the trace-zero matrix. -/
def vectorField (M : sl2C) (z : ℂ) : ℂ :=
  -c M * z ^ 2 + (2 : ℂ) * a M * z + b M

/-- The quadratic discriminant of the infinitesimal vector field. -/
def discriminant (M : sl2C) : ℂ :=
  (2 : ℂ) ^ 2 * (a M) ^ 2 + (4 : ℂ) * b M * c M

@[simp] theorem matrix_00 (M : sl2C) : M.matrix 0 0 = a M := by rfl
@[simp] theorem matrix_01 (M : sl2C) : M.matrix 0 1 = b M := by rfl
@[simp] theorem matrix_10 (M : sl2C) : M.matrix 1 0 = c M := by rfl

@[simp] theorem matrix_11 (M : sl2C) : M.matrix 1 1 = -a M := by
  have h : M.matrix 0 0 + M.matrix 1 1 = 0 := by
    simpa [Matrix.trace, matrix] using M.2
  change M.matrix 1 1 = -M.matrix 0 0
  linear_combination h

@[simp] theorem matrix_trace_zero (M : sl2C) : M.matrix 0 0 + M.matrix 1 1 = 0 := by
  simpa [Matrix.trace, matrix] using M.2

theorem matrix_det (M : sl2C) : M.matrix.det = -(M.a ^ 2 + M.b * M.c) := by
  rw [Matrix.det_fin_two, matrix_00, matrix_01, matrix_10, matrix_11]
  ring

theorem discriminant_eq_four_mul (M : sl2C) :
    M.discriminant = (4 : ℂ) * (M.a ^ 2 + M.b * M.c) := by
  dsimp [discriminant]
  ring

theorem discriminant_eq_neg_four_det (M : sl2C) :
    M.discriminant = (-4 : ℂ) * M.matrix.det := by
  rw [matrix_det, discriminant_eq_four_mul]
  ring

/-- Parabolic sample: repeated root because the discriminant vanishes. -/
def parabolic : sl2C := ofCoords 1 1 (-1)

/-- Hyperbolic sample: real positive discriminant. -/
def hyperbolic : sl2C := ofCoords 1 0 (-1)

/-- Elliptic sample: real negative discriminant. -/
def elliptic : sl2C := ofCoords 0 1 (-1)

/-- Loxodromic sample: non-real discriminant. -/
def loxodromic : sl2C := ofCoords 1 1 Complex.I

theorem parabolic_vectorField (z : ℂ) :
    parabolic.vectorField z = z ^ 2 + 2 * z + 1 := by
  simp [parabolic, ofCoords, vectorField, a, b, c]

theorem hyperbolic_vectorField (z : ℂ) :
    hyperbolic.vectorField z = z ^ 2 + 2 * z := by
  simp [hyperbolic, ofCoords, vectorField, a, b, c]

theorem elliptic_vectorField (z : ℂ) :
    elliptic.vectorField z = z ^ 2 + 1 := by
  simp [elliptic, ofCoords, vectorField, a, b, c]

theorem parabolic_discriminant : parabolic.discriminant = 0 := by
  norm_num [parabolic, ofCoords, discriminant, a, b, c]

theorem hyperbolic_discriminant : hyperbolic.discriminant = 4 := by
  norm_num [hyperbolic, ofCoords, discriminant, a, b, c]

theorem elliptic_discriminant : elliptic.discriminant = -4 := by
  norm_num [elliptic, ofCoords, discriminant, a, b, c]

theorem loxodromic_discriminant : loxodromic.discriminant = 4 + 4 * Complex.I := by
  simp [loxodromic, ofCoords, discriminant, a, b, c]
  ring_nf

theorem loxodromic_discriminant_im_ne_zero : loxodromic.discriminant.im ≠ 0 := by
  norm_num [loxodromic_discriminant]

end sl2C

end InfoGeometry.Geometry
