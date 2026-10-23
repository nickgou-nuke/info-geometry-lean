/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.DrazinNilpotentShellResolution

/-!
# Axiom audit: Drazin nilpotent shell resolution

Kernel audit of the generic shell filtration and its Drazin-dressed resolution.
The statements live over an arbitrary `[Ring R] [StarRing R]`; the matrix-level
owners `InfoGeometry.Singular.NilpotentShellFiltration` and
`InfoGeometry.Singular.NilpotentShellAbsorption` are the `Matrix n n ℝ`
instances of the raw shell layer.

The dressed layer is new: it composes the generic Drazin core/nilpotent split
with the raw shell filtration, without assuming commutativity, diagonalizability,
or symmetry of the complementary projector.
-/

open InfoGeometry.Canonical.DrazinNilpotentShell

#print axioms PowerMPFamily
#print axioms rangeProj
#print axioms shellProj
#print axioms rangeProj_zero
#print axioms rangeProj_mul_of_le
#print axioms rangeProj_mul_of_ge
#print axioms rangeProj_mul
#print axioms shellProj_idem
#print axioms shellProj_orthogonal
#print axioms rangeProj_mul_pow
#print axioms shellProj_mul_pow_eq_zero
#print axioms shellProj_recover
#print axioms shellProj_right_absorption_iff
#print axioms shellProj_partition_of_unity
#print axioms nilpotent_shell_projectors_orthogonal_partition

#print axioms complementaryProjection_mul_fittingNilpotentPart
#print axioms complementaryProjection_mul_fittingNilpotentPart_pow
#print axioms complementaryProjection_mul_fittingNilpotentPart_pow_eq
#print axioms complementaryProjection_mul_pow_eq
#print axioms complementaryProjection_mul_pow_eq_fittingNilpotentPart_pow
#print axioms complementaryProjection_mul_fittingNilpotentPart_pow_k
#print axioms fittingNilpotentPart_pow_k_eq_zero
#print axioms complementaryProjection_mul_rangeProj_of_one_le
#print axioms complementaryProjection_mul_shellProj_of_one_le
#print axioms drazinRangeProj_eq_rangeProj_mul_of_one_le
#print axioms drazinRangeProj_mul_of_le
#print axioms drazinRangeProj_mul_of_ge
#print axioms drazinRangeProj_mul
#print axioms drazinShellProj_eq_sub
#print axioms drazinShellProj_eq_right_mul
#print axioms rangeProj_mul_complementaryProjection_of_one_le
#print axioms drazinShellProj_eq_left_mul_of_symm
#print axioms drazinShellProj_idem
#print axioms drazinShellProj_orthogonal
#print axioms projection_drazinShellProj_orthogonal
#print axioms sum_drazinShellProj_eq_complementaryProjection
#print axioms projection_add_sum_drazinShellProj
#print axioms projection_add_sum_left_mul_shellProj
#print axioms drazinShellProj_mul_pow_succ_eq_zero
#print axioms drazinShellProj_not_absorbed_at_m
#print axioms projection_pow_eq_projection
#print axioms projection_mul_pow_mul_pow_eq_projection
#print axioms fittingNilpotentPart_pow_eq_pow_mul_complementaryProjection
#print axioms fittingNilpotentPart_pow_mul_complementaryProjection
#print axioms drazinShellProj_zero_mul_eq_zero
#print axioms drazin_core_and_nilpotent_shells_partition_of_unity
