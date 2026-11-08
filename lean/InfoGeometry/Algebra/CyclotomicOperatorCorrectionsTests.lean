import InfoGeometry.Algebra.CubicCompanionFlow
import InfoGeometry.Algebra.SplitCliffordOperatorModes
import InfoGeometry.Algebra.MoebiusTraceInvariant
import InfoGeometry.Algebra.ParabolicJordanZorn

open InfoGeometry.Algebra
open SplitQuaternionMatrices

example : (sqI * sqJ) ^ 2 = 1 :=
  SplitCliffordOperatorModes.anticommuting_product_sq sqI sqJ
    sqI_sq sqJ_sq (by simp)

example : (sqI * sqJ) * sqI * (sqI * sqJ) = -sqI :=
  SplitCliffordOperatorModes.anticommuting_product_conjugates sqI sqJ sqI_sq sqJ_sq

example : Pplus * Pplus ≠ 0 :=
  SplitCliffordOperatorModes.positive_projector_not_square_zero

example : orderOf LieCyclotomicBridge.thirdRoot = 3 :=
  LieCyclotomicBridge.thirdRoot_order

example : orderOf LieCyclotomicBridge.fourthRoot = 4 :=
  LieCyclotomicBridge.fourthRoot_order

#print axioms CubicCompanionFlow.exp_generator
#print axioms SplitCliffordOperatorModes.split_mixed_square
#print axioms SplitCliffordOperatorModes.split_null_exponential
#print axioms MoebiusTraceInvariant.traceRatio_smul
#print axioms MoebiusTraceInvariant.complex_example_nonreal
#print axioms MoebiusTraceInvariant.imaginary_parameter_traceRatio
#print axioms ParabolicJordanZorn.eigenspace_one_finrank
#print axioms ParabolicJordanZorn.not_similar_to_diagonal
#print axioms ParabolicJordanZorn.shear_no_positive_period
