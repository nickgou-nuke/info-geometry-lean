import InfoGeometry.OperatorAlgebra.PeirceTracePairing
import InfoGeometry.OperatorAlgebra.OperatorDiracSchur

/-!
# Dense noncommuting regression witnesses

These are tests of the general operator theorems, not substitutes for them.
The idempotent and the two test operators have no zero entries. In particular
no diagonalization or commutation hypothesis conceals the mixed defect.
-/

namespace InfoGeometry.OperatorAlgebra.LieJordanPeirceExamples

open Matrix LieJordanDuality PeirceLieJordanResolution
open InfoGeometry.Algebra.PeirceDeWittChiralSplit

def projection : Matrix (Fin 2) (Fin 2) ℚ := !![2, -1; 2, -1]
def firstOp : Matrix (Fin 2) (Fin 2) ℚ := !![1, 2; 3, 4]
def secondOp : Matrix (Fin 2) (Fin 2) ℚ := !![2, 3; 5, 7]

theorem projection_idempotent : projection * projection = projection := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [projection, Matrix.mul_apply, Fin.sum_univ_two]

/-- The two dense inputs genuinely do not commute. -/
theorem inputs_noncommuting : firstOp * secondOp ≠ secondOp * firstOp := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℚ => M 0 0) h
  norm_num [firstOp, secondOp, Matrix.mul_apply, Fin.sum_univ_two] at h00

/-- The sign error in the supplied ordered dual-product prose is observable. -/
theorem mixed_defect_nonzero :
    jordan ℚ (firstOp * secondOp - secondOp * firstOp) projection ≠ 0 := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℚ => M 0 0) h
  norm_num [jordan_apply, firstOp, secondOp, projection,
    Matrix.mul_apply, Fin.sum_univ_two] at h00

/-- The weighted bilinear trace is not a symmetric metric on all matrices. -/
theorem weighted_pairing_nonsymmetric :
    trace (grading projection * firstOp * secondOp) ≠
      trace (grading projection * secondOp * firstOp) := by
  norm_num [grading, compIdempotent, projection, firstOp, secondOp,
    Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two]

/-- The original complementary-corner identity is correct, with its minus sign. -/
theorem source_complementary_identity :
    2 • peirce00 projection firstOp =
      2 • firstOp - jordan ℚ projection firstOp - ad ℚ projection (ad ℚ projection firstOp) := by
  exact twice_peirce00 ℚ projection_idempotent firstOp

/-- The positive-sign variant introduced during intake review is false. -/
theorem positive_sign_variant_false :
    2 • peirce00 projection firstOp ≠
      2 • firstOp - jordan ℚ projection firstOp + ad ℚ projection (ad ℚ projection firstOp) := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℚ => M 0 0) h
  norm_num [peirce00, compIdempotent, jordan_apply, ad_apply, projection, firstOp,
    two_nsmul, Matrix.mul_apply, Fin.sum_univ_two] at h00

end InfoGeometry.OperatorAlgebra.LieJordanPeirceExamples
