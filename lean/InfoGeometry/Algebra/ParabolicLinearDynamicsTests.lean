import InfoGeometry.Algebra.ParabolicLinearDynamics

namespace InfoGeometry.Algebra.ParabolicLinearDynamics

open InfoGeometry.Clifford.Cl11Matrix
open InfoGeometry.GrandUnification.Matrix2KANPauliChain

example (parameter : ℝ) (state : Mat2) :
    differential parameter (differential parameter state) = 0 :=
  differential_squared parameter state

example (state : Mat2) : chiralSwitch (chiralSwitch state) = state :=
  chiralSwitch_involutive state

example (parameter : ℝ) (state : Mat2) :
    flow (-parameter) (flow parameter state) = state :=
  flow_reversible parameter state

example : combinedOperator 0 0 (0 : Mat2) ≠ (1 : Mat2) := by
  rw [combinedOperator_zero]
  exact zero_ne_one

example (shearParameter timeParameter : ℝ) (first second : Mat2) :
    combinedOperator shearParameter timeParameter (first + second) =
      combinedOperator shearParameter timeParameter first +
        combinedOperator shearParameter timeParameter second :=
  map_add _ _ _

example : (!![(1 : ℝ), 0; 0, 0] : Mat2)ᵀ * !![1, 0; 0, 0] ≠ 1 := by
  intro hequal
  have hentry := congrArg (fun matrix : Mat2 => matrix 1 1) hequal
  norm_num [Matrix.mul_apply, Fin.sum_univ_two] at hentry

example : (!![(0 : ℝ), 0; 1, 0] : Mat2)ᵀ * !![0, 0; 1, 0] ≠ 1 := by
  intro hequal
  have hentry := congrArg (fun matrix : Mat2 => matrix 1 1) hequal
  norm_num [Matrix.mul_apply, Fin.sum_univ_two] at hentry

example : symmetricDifferentialMatrix 2 ^ 2 = (4 : ℝ) • (1 : Mat2) := by
  rw [symmetricDifferentialMatrix_square]
  norm_num

#print axioms differential_range_le_ker
#print axioms chiralSwitch_involutive
#print axioms flow_reversible
#print axioms combinedOperator_static
#print axioms symmetricDifferentialMatrix_square
#print axioms no_two_orthogonal_matrix_isometries

end InfoGeometry.Algebra.ParabolicLinearDynamics
