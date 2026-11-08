import InfoGeometry.SuperGrassmannian.RealSuperGrassmannianModule
import InfoGeometry.SuperGrassmannian.RealSuperGrassmannianOperatorBlocks

open InfoGeometry.SuperGrassmannian.RealSuperGrassmannianModule

/-!
# Audit of Scalar 1|1 Identities and Noncommutative Operator-Block Supertrace

This diagnostic file prints axiom signatures for the scalar-entry `1|1`
identities and the finite operator-block bridge. The `#print axioms` commands
expose Lean's dependency data; they do not themselves enforce an allowlist or
check for proof holes. Enforcement and kernel compilation are separate QMS
steps. The carrier and theorem scopes are described in the owner files.
-/

-- 1. Graded Decomposition & Projections
#print axioms SuperMatrix.even_add_odd
#print axioms SuperMatrix.evenPart_is_even
#print axioms SuperMatrix.oddPart_is_odd
#print axioms SuperMatrix.evenPart_even
#print axioms SuperMatrix.oddPart_odd

-- 2. Graded Ring Multiplication Rules
#print axioms SuperMatrix.even_mul_even
#print axioms SuperMatrix.odd_mul_odd
#print axioms SuperMatrix.even_mul_odd
#print axioms SuperMatrix.odd_mul_even

-- 3. Graded Supertrace Linearity
#print axioms SuperMatrix.supertrace_zero
#print axioms SuperMatrix.supertrace_add
#print axioms SuperMatrix.supertrace_sub
#print axioms SuperMatrix.supertrace_neg
#print axioms SuperMatrix.supertrace_smul
#print axioms SuperMatrix.supertrace_odd

-- 4. Supercommutator Cyclicity & Superbracket Annihilation
#print axioms SuperMatrix.supertrace_even_supercommutator
#print axioms SuperMatrix.supertrace_odd_supercommutator
#print axioms SuperMatrix.supertrace_mixed_supercommutator_even_odd
#print axioms SuperMatrix.supertrace_mixed_supercommutator_odd_even
#print axioms SuperMatrix.supertrace_superbracket_eq_zero

-- 5. Diagonal Scalar Idempotent Pairs
#print axioms SuperMatrix.projector_is_even
#print axioms SuperMatrix.projector_idempotent
#print axioms SuperMatrix.projector_supertrace
#print axioms SuperMatrix.balanced_projector_supertrace_zero

-- 6. Diagonal Quotient and Entrywise Exponential Identities
#print axioms SuperMatrix.berezinian_one
#print axioms SuperMatrix.berezinian_mul_even
#print axioms SuperMatrix.balanced_berezinian_one
#print axioms SuperMatrix.upperShear_evenPart
#print axioms SuperMatrix.lowerShear_evenPart
#print axioms SuperMatrix.berezinian_exp_even
#print axioms SuperMatrix.supertraceless_berezinian_exp_one

-- 7. Scalar-Pair Action-Like Operation
#print axioms SuperModule.act_one
#print axioms SuperModule.act_mul
#print axioms SuperModule.act_add
#print axioms SuperModule.act_vec_add
#print axioms SuperModule.act_even_preserves_grading_plus
#print axioms SuperModule.act_even_preserves_grading_minus
#print axioms SuperModule.act_odd_reverses_grading_plus
#print axioms SuperModule.act_odd_reverses_grading_minus

-- 8. Scalar-Model Certificate and Noncommutative Operator-Block Bridge
#print axioms compile_scalar_one_one_graded_algebra
#print axioms InfoGeometry.SuperGrassmannian.RealSuperGrassmannianOperatorBlocks.operator_block_superbracket_supertrace_zero
#print axioms InfoGeometry.SuperGrassmannian.RealSuperGrassmannianOperatorBlocks.finite_operator_block_exp_ratio_law
#print axioms InfoGeometry.SuperGrassmannian.RealSuperGrassmannianOperatorBlocks.concrete_operator_blocks_noncommute
#print axioms InfoGeometry.SuperGrassmannian.RealSuperGrassmannianOperatorBlocks.compile_finite_operator_block_certificate
