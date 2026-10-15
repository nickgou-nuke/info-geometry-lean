import Experimental.Sandbox.SuperGrassmannian.RealSuperGrassmannianModule

open InfoGeometry.SuperGrassmannian.RealSuperGrassmannianModule

/-!
# Audit of Real Super-Grassmannian Module Action, Graded Supertrace, and Berezinian Invariance

This audit file prints the axiom signatures of all key theorems
in `RealSuperGrassmannianModule.lean` to verify:
- 0 `sorry`
- 0 `admit`
- 0 custom axioms (only standard Lean 4 core axioms `[propext, Classical.choice, Quot.sound]`,
  with purely algebraic identities relying strictly on `[propext]` or empty `[]`).
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

-- 5. Super-Grassmannian Idempotent Projectors
#print axioms SuperMatrix.projector_is_even
#print axioms SuperMatrix.projector_idempotent
#print axioms SuperMatrix.projector_supertrace
#print axioms SuperMatrix.balanced_projector_supertrace_zero

-- 6. Berezinian Multiplicativity & Lie Exponential Law
#print axioms SuperMatrix.berezinian_one
#print axioms SuperMatrix.berezinian_mul_even
#print axioms SuperMatrix.balanced_berezinian_one
#print axioms SuperMatrix.upperShear_evenPart
#print axioms SuperMatrix.lowerShear_evenPart
#print axioms SuperMatrix.berezinian_exp_even
#print axioms SuperMatrix.supertraceless_berezinian_exp_one

-- 7. Graded Super-Module Action on S+ ⊕ S-
#print axioms SuperModule.act_one
#print axioms SuperModule.act_mul
#print axioms SuperModule.act_add
#print axioms SuperModule.act_vec_add
#print axioms SuperModule.act_even_preserves_grading_plus
#print axioms SuperModule.act_even_preserves_grading_minus
#print axioms SuperModule.act_odd_reverses_grading_plus
#print axioms SuperModule.act_odd_reverses_grading_minus

-- 8. Master Verification Certificate
#print axioms compile_real_super_grassmannian_module
