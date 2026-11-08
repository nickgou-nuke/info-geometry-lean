import InfoGeometry.Epistemology.AlchemicalPurification

/-!
# Audit Module: AlchemicalPurificationAudit

Audits and confirms axiom counts for `InfoGeometry.Epistemology.AlchemicalPurification`.
Strictly verifies that all theorems depend only on standard Lean foundational axioms
`[propext, Classical.choice, Quot.sound]` with 0 sorry and 0 admit.
-/

namespace InfoGeometry.Epistemology.AlchemicalPurificationAudit

open InfoGeometry.Epistemology.AlchemicalPurification

#print axioms projector_annihilation
#print axioms projector_annihilation_rev
#print axioms complement_idempotent
#print axioms peirce_orthogonal_sum
#print axioms logSumExp2_hasDerivAt
#print axioms logSumExp2_deriv
#print axioms attention_hessian_hasDerivAt
#print axioms attention_hessian_is_variance
#print axioms fisher_variance_le_quarter
#print axioms fisher_variance_nonneg
#print axioms reflection_reverses_flow
#print axioms reflection_boundary_fixed
#print axioms andreev_parity_involutive
#print axioms winding_stability
#print axioms winding_convex_comb
#print axioms compile_alchemical_purification

end InfoGeometry.Epistemology.AlchemicalPurificationAudit
