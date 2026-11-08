/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.MatrixNoncommutativity
import InfoGeometry.Physics.BdGChiralBlockMatrix
import InfoGeometry.OperatorAlgebra.PeirceCompressionCurvature
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.NormNum

/-!
# The existing BdG operator as a Peirce tangent and curvature insertion

The internal coefficients lie in an arbitrary associative star ring.  They
need not commute.  The first-sheet projection is structural; the tangent
operators retain their full arbitrary off-diagonal operator coefficients.

The ordered two-point coefficient is `a * star b`.  Its alternating part is
`a * star b - b * star a`, exactly the corresponding projector-curvature
corner.  A nested full complex-matrix witness proves this corner can be
nonzero with genuinely noncommuting internal operators.
-/

namespace InfoGeometry.OperatorAlgebra.BdGPeirceCurvature

open InfoGeometry.Physics
open InfoGeometry.OperatorAlgebra.PeirceCompressionCurvature
open InfoGeometry.Clifford.ChiralProjectorBerryCurvature

variable {A : Type*} [Ring A]

/-- First-sector projection in the existing native two-by-two operator block algebra. -/
def firstSheetProjector : BdGBlock A := !![1, 0; 0, 0]

theorem firstSheetProjector_sq :
    firstSheetProjector (A := A) * firstSheetProjector = firstSheetProjector := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [firstSheetProjector, Matrix.mul_apply, Fin.sum_univ_two]

variable [StarRing A]

theorem firstSheetProjector_star :
    star (firstSheetProjector (A := A)) = firstSheetProjector := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [firstSheetProjector]

/-- The existing BdG off-diagonal operator solves the exact idempotent tangent equation. -/
theorem diracOperator_tangent (a : A) :
    firstSheetProjector * diracOperator a +
        diracOperator a * firstSheetProjector = diracOperator a := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [firstSheetProjector, diracOperator]

/-- The complete ordered correlation retains the two arbitrary operator coefficients. -/
theorem compressedGram_diracOperator (a b : A) :
    compressedGram firstSheetProjector (diracOperator a) (diracOperator b) =
      !![a * star b, 0; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [compressedGram, firstSheetProjector, diracOperator,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

/-- Curvature is the alternating ordered intersector correlation. -/
theorem projectorCurvature_diracOperator (a b : A) :
    projectorCurvature firstSheetProjector (diracOperator a) (diracOperator b) =
      !![a * star b - b * star a, 0; 0, 0] := by
  rw [← compressedGram_sub_swap_eq_projectorCurvature firstSheetProjector_sq
    (diracOperator_tangent a) (diracOperator_tangent b),
    compressedGram_diracOperator, compressedGram_diracOperator]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The coefficient vanishes precisely when the two ordered correlations agree. -/
theorem projectorCurvature_diracOperator_eq_zero_iff (a b : A) :
    projectorCurvature firstSheetProjector (diracOperator a) (diracOperator b) = 0 ↔
      a * star b = b * star a := by
  rw [projectorCurvature_diracOperator]
  constructor
  · intro h
    have hcorner := congrArg (fun M : BdGBlock A => M 0 0) h
    apply sub_eq_zero.mp
    simpa using hcorner
  · intro h
    rw [h, sub_self]
    ext i j
    fin_cases i <;> fin_cases j <;> simp

/-- Noncommuting internal operators can produce nonzero curvature on the
full nested operator carrier; neither coefficient is restricted to a scalar. -/
theorem exists_noncommuting_coefficients_with_nonzero_curvature :
    ∃ a b : Matrix (Fin 2) (Fin 2) ℂ,
      a * b ≠ b * a ∧
      projectorCurvature firstSheetProjector (diracOperator a) (diracOperator b) ≠ 0 := by
  let a : Matrix (Fin 2) (Fin 2) ℂ :=
    InfoGeometry.Algebra.MatrixNoncommutativity.swapMatrix
  let b : Matrix (Fin 2) (Fin 2) ℂ :=
    InfoGeometry.Algebra.MatrixNoncommutativity.tiltedMatrix
  have ha : star a = a :=
    InfoGeometry.Algebra.MatrixNoncommutativity.star_swapMatrix
  have hb : star b = b :=
    InfoGeometry.Algebra.MatrixNoncommutativity.star_tiltedMatrix
  have hnc : a * b ≠ b * a :=
    InfoGeometry.Algebra.MatrixNoncommutativity.swapMatrix_mul_tiltedMatrix_ne
  refine ⟨a, b, hnc, ?_⟩
  intro hcurv
  have h := (projectorCurvature_diracOperator_eq_zero_iff a b).mp hcurv
  rw [ha, hb] at h
  exact hnc h

end InfoGeometry.OperatorAlgebra.BdGPeirceCurvature
