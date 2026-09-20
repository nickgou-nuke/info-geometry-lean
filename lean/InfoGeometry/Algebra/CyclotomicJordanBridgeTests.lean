import InfoGeometry.Algebra.LieCyclotomicBridge
import InfoGeometry.Algebra.SplitCliffordOperatorIdentities
import InfoGeometry.Algebra.ParabolicJordanZorn
import InfoGeometry.Geometry.MoebiusModeExamples

namespace InfoGeometry.Algebra.CyclotomicJordanBridgeTests

open InfoGeometry.Clifford.Cl11Matrix
open InfoGeometry.GrandUnification.Matrix2KANPauliChain
open LieCyclotomicBridge ParabolicJordanZorn
open scoped Matrix.Norms.Operator

example : orderOf thirdRoot = 3 := thirdRoot_order

example : orderOf fourthRoot = 4 := fourthRoot_order

example : NormedSpace.exp ((Real.pi / 2) • fourthRoot) = fourthRoot :=
  exp_pi_half_fourthRoot

example : Module.finrank ℝ ((shearEnd 2).eigenspace 1) = 1 :=
  eigenspace_one_finrank 2 (by norm_num)

example (exponent : ℕ) (hpositive : 0 < exponent) : NPart 2 ^ exponent ≠ 1 :=
  shear_no_positive_period 2 (by norm_num) exponent hpositive

example : (Eminus + Eplus) ^ 2 = 0 := by
  simpa using SplitCliffordOperatorIdentities.mixed_generator_square 1 1

example : (NPart 0 - 1) = 0 := by
  rw [(MatrixCyclotomics.NPart_eq_one_iff 0).mpr rfl, sub_self]

example : InfoGeometry.IsLoxodromic
    InfoGeometry.Geometry.MoebiusModeExamples.realDiscriminantLoxodromicExample :=
  InfoGeometry.Geometry.MoebiusModeExamples.realDiscriminantLoxodromicExample_isLoxodromic

#print axioms thirdRoot_order
#print axioms fourthRoot_order
#print axioms exp_pi_half_fourthRoot
#print axioms eigenspace_one_finrank
#print axioms not_similar_to_diagonal
#print axioms shear_no_positive_period
#print axioms SplitCliffordOperatorIdentities.mixed_product_square
#print axioms InfoGeometry.Geometry.MoebiusModeExamples.loxodromic_can_have_real_negative_discriminant

end InfoGeometry.Algebra.CyclotomicJordanBridgeTests
