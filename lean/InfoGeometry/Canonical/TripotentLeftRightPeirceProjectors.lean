import InfoGeometry.Physics.Algebra.TripotentLeftRightPeirceProjectors

/-!
# Canonical namespace for the left/right Peirce calculus

The constructive owner is
`InfoGeometry.Physics.Algebra.TripotentLeftRightPeirceProjectors`.
This file is a compatibility export, so canonical consumers use the same
kernel-checked definitions and proofs without a second implementation.
-/

namespace InfoGeometry.Canonical.TripotentLeftRightPeirceProjectors

export InfoGeometry.Physics.Algebra
  (leftMulOp rightMulOp leftMulOp_apply rightMulOp_apply
   leftMulOp_comp_rightMulOp leftMulOp_tripotent rightMulOp_tripotent
   PeirceSign peirceScalar peirceProjector peirceProjector_pos
   peirceProjector_zero peirceProjector_neg peirceProjectors_sum_eq_one
   peirceProjector_idempotent peirceProjector_mul_eq_zero_of_ne
   e_mul_peirceProjector peirceProjector_mul_e leftPeirceProjector
   rightPeirceProjector jointPeirceProjector leftPeirceProjector_apply
   rightPeirceProjector_apply jointPeirceProjector_apply
   jointPeirceProjector_idempotent
   jointPeirceProjector_mul_eq_zero_of_left_ne
   jointPeirceProjector_mul_eq_zero_of_right_ne
   jointPeirce_reconstruction jointPeirceProjector_adjoint_weight
   gradePosTwoProjector gradePosOneProjector gradeZeroProjector
   gradeNegOneProjector gradeNegTwoProjector fiveGradeProjectors_sum_eq_id
   gradePosTwo_adjoint_weight gradeNegTwo_adjoint_weight
   gradePosOne_adjoint_weight gradeNegOne_adjoint_weight
   gradeZero_adjoint_weight)

end InfoGeometry.Canonical.TripotentLeftRightPeirceProjectors
