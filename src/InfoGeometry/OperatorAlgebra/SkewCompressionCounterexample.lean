/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.SkewCompressionGap
import InfoGeometry.OperatorAlgebra.FinitePropagationCompression
import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# A finite skew matrix with a boundary zero mode and unit compressed square

The real matrix has a two-coordinate skew block and one additional zero
coordinate. The cut retains only the first coordinate. Its square-first
compression is the identity on that coordinate, although the compressed
skew operator vanishes and the full operator has a nonzero kernel vector.

This is a concrete finite-matrix example. It is not a theorem about the
spectrum of a physical edge Hamiltonian or an infinite lattice.
-/

namespace InfoGeometry.OperatorAlgebra.SkewCompressionCounterexample

open InfoGeometry.OperatorAlgebra.SkewCompressionGap
open InfoGeometry.OperatorAlgebra.FinitePropagationCompression
open scoped Matrix

/-- The cut retains the first of three coordinate vectors. -/
def bulkCut : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, 0, 0; 0, 0, 0; 0, 0, 0]

/-- A unit skew block on coordinates zero and one, extended by zero at coordinate two. -/
def bulkSkew : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, 1, 0; -1, 0, 0; 0, 0, 0]

/-- The omitted third coordinate is a zero mode of the full skew operator. -/
def boundaryVector : Fin 3 → ℝ := ![0, 0, 1]

theorem bulkCut_eq_coordinateProjection :
    bulkCut = coordinateProjection ({0} : Finset (Fin 3)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bulkCut, coordinateProjection]

@[simp] theorem bulkCut_mul_self : bulkCut * bulkCut = bulkCut := by
  rw [bulkCut_eq_coordinateProjection, coordinateProjection_mul_self]

@[simp] theorem star_bulkCut : star bulkCut = bulkCut := by
  rw [bulkCut_eq_coordinateProjection, star_coordinateProjection]

/-- The example is genuinely skew-adjoint in the native full matrix star ring. -/
theorem star_bulkSkew : star bulkSkew = -bulkSkew := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bulkSkew]

/-- The cut and skew matrix do not commute. -/
theorem bulkCut_mul_bulkSkew_ne : bulkCut * bulkSkew ≠ bulkSkew * bulkCut := by
  intro h
  have hentry := congrArg (fun a : Matrix (Fin 3) (Fin 3) ℝ => a 0 1) h
  norm_num [bulkCut, bulkSkew, Matrix.mul_apply, Fin.sum_univ_three] at hentry

theorem bulkCut_ne_zero : bulkCut ≠ 0 := by
  intro h
  have hentry := congrArg (fun a : Matrix (Fin 3) (Fin 3) ℝ => a 0 0) h
  norm_num [bulkCut] at hentry

/-- Truncating the skew operator first removes both off-diagonal couplings. -/
theorem compressed_bulkSkew_eq_zero : bulkCut * bulkSkew * bulkCut = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [bulkCut, bulkSkew, Matrix.mul_apply, Fin.sum_univ_three]

/-- Squaring before compression retains a unit positive operator on the selected coordinate. -/
theorem compressed_negative_square_eq_cut :
    bulkCut * (-(bulkSkew * bulkSkew)) * bulkCut = bulkCut := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [bulkCut, bulkSkew, Matrix.mul_apply, Fin.sum_univ_three]

/-- The entire difference is the nonzero exterior-transfer Gram operator. -/
theorem exterior_gram_eq_cut :
    star ((1 - bulkCut) * bulkSkew * bulkCut) *
        ((1 - bulkCut) * bulkSkew * bulkCut) = bulkCut := by
  rw [← negative_square_compression_defect_eq_gram bulkCut bulkSkew
    bulkCut_mul_self star_bulkCut star_bulkSkew,
    compressed_negative_square_eq_cut, compressed_bulkSkew_eq_zero]
  simp

theorem exterior_gram_ne_zero :
    star ((1 - bulkCut) * bulkSkew * bulkCut) *
        ((1 - bulkCut) * bulkSkew * bulkCut) ≠ 0 := by
  rw [exterior_gram_eq_cut]
  exact bulkCut_ne_zero

/-- Positive semidefiniteness follows from the general skew-compression theorem. -/
theorem square_first_posSemidef :
    (bulkCut * (-(bulkSkew * bulkSkew)) * bulkCut).PosSemidef := by
  have h := negative_square_compression_defect_posSemidef bulkCut bulkSkew
    bulkCut_mul_self star_bulkCut star_bulkSkew
  simpa only [compressed_bulkSkew_eq_zero, zero_mul, add_zero] using h

/-- Centering the square-first operator at one gives zero on the selected corner. -/
theorem centered_square_first_eq_zero :
    bulkCut * (-(bulkSkew * bulkSkew) - 1) * bulkCut = 0 := by
  calc
    bulkCut * (-(bulkSkew * bulkSkew) - 1) * bulkCut =
        bulkCut * (-(bulkSkew * bulkSkew)) * bulkCut - bulkCut * bulkCut := by
          noncomm_ring
    _ = 0 := by rw [compressed_negative_square_eq_cut, bulkCut_mul_self, sub_self]

/-- In the opposite order, the same centering leaves a nonzero negative cut. -/
theorem centered_truncate_first_eq_neg_cut :
    -((bulkCut * bulkSkew * bulkCut) * (bulkCut * bulkSkew * bulkCut)) -
        bulkCut * bulkCut = -bulkCut := by
  rw [compressed_bulkSkew_eq_zero, bulkCut_mul_self]
  simp

theorem boundaryVector_ne_zero : boundaryVector ≠ 0 := by
  intro h
  have hentry := congrFun h 2
  norm_num [boundaryVector] at hentry

/-- The full matrix has an actual nonzero kernel vector, not merely a zero diagonal entry. -/
theorem bulkSkew_mulVec_boundary_eq_zero : bulkSkew *ᵥ boundaryVector = 0 := by
  ext i
  fin_cases i <;>
    norm_num [bulkSkew, boundaryVector, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- The exhibited zero mode lies outside the selected interior coordinate. -/
theorem bulkCut_mulVec_boundary_eq_zero : bulkCut *ᵥ boundaryVector = 0 := by
  ext i
  fin_cases i <;>
    norm_num [bulkCut, boundaryVector, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- With the three coordinates at positions `0, 1, 2`, the skew matrix has range one. -/
theorem bulkSkew_propagation_one :
    HasPropagationAtMost (fun i : Fin 3 => (i.val : ℝ)) 1 bulkSkew := by
  intro i j hfar
  fin_cases i <;> fin_cases j <;>
    norm_num [bulkSkew, Real.dist_eq] at *

end InfoGeometry.OperatorAlgebra.SkewCompressionCounterexample
