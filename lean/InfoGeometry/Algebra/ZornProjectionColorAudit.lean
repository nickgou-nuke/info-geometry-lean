import InfoGeometry.Algebra.ZornRightProjectionObstruction
import InfoGeometry.Algebra.ZornColorGL31Obstruction

/-! Audit of native operator replacements for the projection and color-action
obstructions. This does not identify the color space with gl(3|1). -/

open InfoGeometry.Algebra.ZornVectorMatrix
open InfoGeometry.Algebra.ZornColorOperatorCoordinates

#print axioms right_E22_offDiagonal_tangent_defect
#print axioms right_E22_offDiagonal_tangent_iff
#print axioms right_E22_offDiagonal_tangent_operator_iff
#print axioms right_E22_upper_not_tangent
#print axioms left_E11_idempotent
#print axioms left_E11_tangent_offDiagonal
#print axioms left_diagonal_difference_involution
#print axioms left_diagonal_difference_anticommutes_offDiagonal
#print axioms gl31_odd_bracket_noncentral
#print axioms not_faithful_gl31_with_CAR_odd
#print axioms explicit_anomaly_in_kernel_of_homogeneous_bracket_map_to_CAR_odd
#print axioms gl3Representation_injective
#print axioms oddDerived_eq_scalar
#print axioms finrank_oddDerived
#print axioms finrank_color_operator_space
#print axioms bracket_mem
#print axioms homogeneous_super_jacobi
