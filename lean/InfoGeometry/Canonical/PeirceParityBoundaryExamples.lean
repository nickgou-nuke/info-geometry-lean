/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.PeirceParityClosure
import InfoGeometry.Core.PeirceTangentCounterexample
import InfoGeometry.Canonical.AnomalyStrainRotationWitness

/-!
# Boundary examples for native Peirce parity

Reuses the existing characteristic-two matrices
and the actual Moore--Penrose source/penrose witness. These examples separate
sign-fixedness from even parity, refute unconditional tripotence of the MP
support difference, and exhibit an odd sum whose square is one. No Lie-type
classification, new matrix carrier, or general spectral claim is asserted.
-/

namespace InfoGeometry.Canonical.PeirceParityBoundaryExamples

open InfoGeometry.Algebra.PeirceDeWittChiralSplit
open InfoGeometry.Core.PeirceTangent
open InfoGeometry.Canonical.AnomalyStrainRotationWitness

noncomputable section

/-- The native boundary endpoint is a genuine idempotent. -/
theorem boundary_projection_idempotent : IsIdempotent matrixBoundaryProjection :=
  matrix_reflection_anticommutation_not_tangent.1

/-- In characteristic two this idempotent's native grading is the identity. -/
theorem boundary_grading_eq_one :
    grading matrixBoundaryProjection = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [grading, compIdempotent, matrixBoundaryProjection]
  all_goals decide

theorem boundary_direction_sign_fixed :
    grading matrixBoundaryProjection * matrixBoundaryDirection *
      grading matrixBoundaryProjection = matrixBoundaryDirection := by
  rw [boundary_grading_eq_one, one_mul, mul_one]

/-- The off-diagonal coordinate survives even though conjugation fixes it. -/
theorem boundary_direction_oddPart_ne_zero :
    oddPart matrixBoundaryProjection matrixBoundaryDirection ≠ 0 := by
  intro h
  have h01 := congrArg (fun C : Matrix (Fin 2) (Fin 2) (ZMod 2) => C 0 1) h
  norm_num [oddPart, peirce10, peirce01, compIdempotent,
    matrixBoundaryProjection, matrixBoundaryDirection,
    Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_apply, Fin.sum_univ_two] at h01

theorem boundary_direction_not_even :
    evenPart matrixBoundaryProjection matrixBoundaryDirection ≠ matrixBoundaryDirection := by
  intro h
  have h01 := congrArg (fun C : Matrix (Fin 2) (Fin 2) (ZMod 2) => C 0 1) h
  norm_num [evenPart, peirce11, peirce00, compIdempotent,
    matrixBoundaryProjection, matrixBoundaryDirection,
    Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_apply, Fin.sum_univ_two] at h01

/-- An explicit failure of the positive-sign converse without injective doubling. -/
theorem sign_fixed_does_not_force_even :
    ¬ (∀ x : Matrix (Fin 2) (Fin 2) (ZMod 2),
      grading matrixBoundaryProjection * x * grading matrixBoundaryProjection = x →
        evenPart matrixBoundaryProjection x = x) := by
  intro h
  exact boundary_direction_not_even (h matrixBoundaryDirection boundary_direction_sign_fixed)

/-- The 00 coefficient of the cube is -1/4, whereas that of the difference is -1/2. -/
theorem support_difference_cube_entry00 :
    ((penrose * source - source * penrose) ^ 3) 0 0 = -(1 / 4 : ℝ) := by
  norm_num [source, penrose, pow_succ, Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_apply, Fin.sum_univ_two]

/-- Even with the existing source_moorePenrose witness, the support difference
need not be tripotent. This does not concern the square-zero special case. -/
theorem support_difference_not_tripotent :
    (penrose * source - source * penrose) ^ 3 ≠ penrose * source - source * penrose := by
  intro h
  have h00 := congrArg (fun C : Mat2 => C 0 0) h
  rw [support_difference_cube_entry00] at h00
  norm_num [source, penrose, Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_apply, Fin.sum_univ_two] at h00

/-- Use the existing shear's range support as the Peirce endpoint. -/
theorem shear_support_idempotent : IsIdempotent (shear * star shear) := by
  change (shear * star shear) * (shear * star shear) = shear * star shear
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [shear, Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_apply, Fin.sum_univ_two]

theorem shear_is_odd : oddPart (shear * star shear) shear = shear := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [oddPart, peirce10, peirce01, compIdempotent, shear,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_apply, Fin.sum_univ_two]

theorem star_shear_is_odd : oddPart (shear * star shear) (star shear) = star shear := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [oddPart, peirce10, peirce01, compIdempotent, shear,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_apply, Fin.sum_univ_two]

theorem shear_sum_is_odd :
    oddPart (shear * star shear) (shear + star shear) = shear + star shear := by
  rw [oddPart_add, shear_is_odd, star_shear_is_odd]

/-- The native odd projection can square to one; odd does not mean square-zero. -/
theorem odd_shear_sum_square_one :
    (oddPart (shear * star shear) (shear + star shear)) ^ 2 = (1 : Mat2) := by
  rw [shear_sum_is_odd, pow_two]
  exact normalized_split_pair.1

end

end InfoGeometry.Canonical.PeirceParityBoundaryExamples
