import InfoGeometry.Quantum.ZornDiagonalPurity

namespace InfoGeometry.Quantum.ZornDiagonalPurityTests

open InfoGeometry.Algebra
open InfoGeometry.Algebra.ZornVectorMatrix
open InfoGeometry.Quantum.ZornDiagonalPurity

noncomputable section

example : trace (mul (diagonal (1 : ℝ) 0) (diagonal 1 0)) = 1 := by
  norm_num [trace_diagonal_mul_diagonal]

example : trace (mul (diagonal (0 : ℝ) 1) (diagonal 0 1)) = 1 := by
  norm_num [trace_diagonal_mul_diagonal]

example : trace (mul (diagonal (1 / 2 : ℝ) (1 / 2))
    (diagonal (1 / 2) (1 / 2))) = 1 / 2 := equipartition_trace_square

example : trace (mul (diagonal (2 : ℝ) (-1)) (diagonal 2 (-1))) = 5 := by
  norm_num [trace_diagonal_mul_diagonal]

#print axioms weighted_idempotents
#print axioms diagonal_trace_normalized
#print axioms diagonal_trace_square_completed_square
#print axioms diagonal_trace_square_lower_bound
#print axioms diagonal_trace_square_eq_half_iff
#print axioms diagonal_trace_square_upper_bound
#print axioms equipartition_square
#print axioms equipartition_trace_square
#print axioms equipartition_renyi_two

end

end InfoGeometry.Quantum.ZornDiagonalPurityTests
