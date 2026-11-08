import InfoGeometry.Algebra.BaezF4H3Zorn
import InfoGeometry.Algebra.H3ZornJordanInstance
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.SplitAlbertF4BasisTrace
import InfoGeometry.Canonical.F4ActionMatrixRankCertificateBridge
import InfoGeometry.Canonical.F4ActionMatrixRationalCertificate

open InfoGeometry.Algebra
open InfoGeometry.Algebra.H3Zorn
open InfoGeometry.Canonical.F4ActionMatrix
open InfoGeometry.Canonical.F4ActionMatrixRationalCertificate
open InfoGeometry.Canonical.H3ZornBasis

namespace F4PivotFamilyCandidateRev3

abbrev EndH3 := Module.End ℝ (H3Zorn ℝ)

/-- Exact finite-family readback for the first eight generators. -/
theorem f4Basis_firstEight_apply (i : Fin 8) (x : H3Zorn ℝ) :
    ((f4Basis (⟨i.val, by omega⟩ : Fin 52)).1 : EndH3) x =
      ((h3ZornJordanInnerDerivation h3_diag₁ (h3_off₁₂ i) : EndH3) x) := by
  fin_cases i <;> rfl

/-- The selected pivot column is the row-zero, `J₁₂` coordinate column. -/
theorem first_eight_pivot_index (i : Fin 8) :
    f4ActionPivot (⟨i.val, by omega⟩ : Fin 52) = ⟨3 + i.val, by omega⟩ := by
  fin_cases i <;> rfl

/-- The exact rational certificate coefficient becomes `-1/4` over `ℝ`. -/
theorem first_eight_pivot_value_cast (i : Fin 8) :
    (f4ActionPivotValue (⟨i.val, by omega⟩ : Fin 52) : ℝ) = (-1 / 4 : ℝ) := by
  fin_cases i <;> norm_num [f4ActionPivotValue]

/-- Family-specific native action coordinate, phrased using the existing
matrix readback interfaces instead of unfolding the flattened matrix. -/
theorem first_eight_native_matrix_coordinate (i : Fin 8) :
    f4BasisActionMatrix (⟨i.val, by omega⟩ : Fin 52) 0 ⟨3 + i.val, by omega⟩ =
      (-1 / 4 : ℝ) := by
  rw [f4BasisActionMatrix_readback]
  rw [h3ZornCoordinateBasis_apply, h3ZornCoordinateBasis_repr_apply]
  rw [f4Basis_firstEight_apply i (h3ZornProbe 0)]
  rw [h3ZornJordanInnerDerivation_apply]
  simp only [← candidateJordanMul_eq_mul]
  simp only [candidateJordanMul_trace_formula]
  fin_cases i <;>
    simp [-candidateJordanMul_eq_mul, h3ZornCoordinate, h3ZornProbe, h3_diag₁, h3_off₁₂, zorn_basis,
      H3Zorn.crossProduct, H3Zorn.adjointQuad, H3Zorn.linearTrace,
      ZornVectorMatrix.norm, ZornVectorMatrix.conj, ZornVectorMatrix.neg,
      ZornVectorMatrix.mul, ZornVectorMatrix.sub, ZornVectorMatrix.add,
      ZornVectorMatrix.smul, ZornVectorMatrix.zero, ZornVec3.dot, ZornVec3.cross,
      H3Zorn.add_readback, H3Zorn.sub_readback,
      H3Zorn.smul_readback, H3Zorn.one_readback] <;> norm_num

/-- The flattening witness for a selected pivot is the row-zero matrix
coordinate used above. -/
theorem first_eight_pivot_flat_index (i : Fin 8) :
    f4ActionPivot (⟨i.val, by omega⟩ : Fin 52) =
      ⟨27 * (0 : Fin 27).val + (⟨3 + i.val, by omega⟩ : Fin 27).val, by omega⟩ := by
  rw [first_eight_pivot_index]
  apply Fin.ext
  simp

/-- Native readout at the selected rational-certificate pivot. This proves
eight diagonal equations only; the off-diagonal zero equations are open. -/
theorem first_eight_native_pivot_diagonal (i : Fin 8) :
    f4ActionMatrix (⟨i.val, by omega⟩ : Fin 52)
      (f4ActionPivot (⟨i.val, by omega⟩ : Fin 52)) =
      (f4ActionPivotValue (⟨i.val, by omega⟩ : Fin 52) : ℝ) := by
  calc
    f4ActionMatrix (⟨i.val, by omega⟩ : Fin 52)
        (f4ActionPivot (⟨i.val, by omega⟩ : Fin 52)) =
        f4BasisActionMatrix (⟨i.val, by omega⟩ : Fin 52) 0
          ⟨3 + i.val, by omega⟩ := by
      rw [first_eight_pivot_flat_index]
      exact f4BasisActionMatrix_flatten _ _ _
    _ = (-1 / 4 : ℝ) := first_eight_native_matrix_coordinate i
    _ = (f4ActionPivotValue (⟨i.val, by omega⟩ : Fin 52) : ℝ) :=
      (first_eight_pivot_value_cast i).symm

end F4PivotFamilyCandidateRev3
