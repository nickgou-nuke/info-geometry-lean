import Experimental.Sandbox.ProjectiveKrein.ProjectiveKreinDecomposition

open InfoGeometry.ProjectiveKrein

/-!
# Audit of Projective Krein Space and 3-Mode Decomposition

This audit file prints the axiom signatures of all key theorems
in `ProjectiveKreinDecomposition.lean` to verify:
- 0 `sorry`
- 0 `admit`
- 0 custom axioms (only standard Lean 4 axioms `[propext, Classical.choice, Quot.sound]`, with many lemmas relying on empty `[]` or `[propext]`).
-/

#print axioms majoranaPlus_sq
#print axioms majoranaMinus_sq
#print axioms majorana_anticommute
#print axioms odd_mul_odd_is_even
#print axioms majorana_sq_is_even
#print axioms DoubledKreinSpace.hilbertInner_symm
#print axioms DoubledKreinSpace.hilbertInner_pos
#print axioms rayEquiv_preserves_sign
#print axioms realProjectiveEquiv_antipodal
#print axioms rayEquiv_separates_antipodal
#print axioms gl2N_dimension_sum_exact
#print axioms gl2N_matrix_dim
#print axioms three_mode_pythagorean_decomposition
#print axioms compile_projective_krein_certificate
