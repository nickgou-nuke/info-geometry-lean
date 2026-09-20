import InfoGeometry.Synthesis.CuntzKleinPropagation

namespace InfoGeometry.Synthesis.CuntzKleinPropagationTests

open InfoGeometry.Synthesis.CuntzKleinPropagation
open InfoGeometry.Topology.CantorBoundaryRealClockShift
open InfoGeometry.Topology.CantorBoundaryCuntzO2

example : shift * shift * (1 : BoundaryOperator ℝ) = clock * clock * 1 := by
  apply square_equation_of_anticommute shift clock 1 phase phase_sq
  · simpa only [neg_neg] using (congrArg Neg.neg clock_shift_weyl).symm
  · simp only [mul_one, phase, ← mul_assoc, clock_sq, one_mul]

example : phase * phase * (1 : BoundaryOperator ℝ) = -(1 * 1 * 1) := by
  apply square_equation_of_commute phase 1 1 phase phase_sq
  · exact Commute.one_right phase
  · simp

example : T 0 * branchDifference = (1 : BoundaryOperator ℝ) := first_branch_readout

example : T 1 * branchDifference = (-1 : BoundaryOperator ℝ) := second_branch_readout

#print axioms square_equation_of_anticommute
#print axioms square_equation_of_commute
#print axioms branch_square_equation

end InfoGeometry.Synthesis.CuntzKleinPropagationTests
