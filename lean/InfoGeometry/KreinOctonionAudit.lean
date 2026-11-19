/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.ZornAssociativeCollapse
import InfoGeometry.Krein.KreinAdjointBoundary
import InfoGeometry.Krein.DoubledKreinWitnesses
import InfoGeometry.Order.KreinOctonionDependencyPoset
import InfoGeometry.Algebra.ZornLeftMultiplicationDefect

/-!
# Krein--octonion import and axiom audit

This leaf imports the four new theorem owners and inspects the axiom footprint
of every exported new theorem. The additional existing-owner checks cover the
actual native left action, its associator defect, and the doubled generators.

The commands print dependencies when Lean checks this module. Their presence
alone does not certify compilation or any stronger physical interpretation.
No theorem wrappers or additional assumptions are introduced here.
-/

/-! ## InfoGeometry.Algebra.ZornAssociativeCollapse -/

#print axioms InfoGeometry.Algebra.ZornVectorMatrix.basis_associator_mul_self
#print axioms InfoGeometry.Algebra.ZornVectorMatrix.additiveMap_associator_eq_zero
#print axioms InfoGeometry.Algebra.ZornVectorMatrix.additiveMap_one_eq_zero
#print axioms InfoGeometry.Algebra.ZornVectorMatrix.additiveMap_eq_zero_of_multiplicative
#print axioms InfoGeometry.Algebra.ZornVectorMatrix.linearMap_eq_zero_of_multiplicative
#print axioms InfoGeometry.Algebra.ZornVectorMatrix.no_unital_additive_multiplicative_map

/-! ## InfoGeometry.Krein.KreinAdjointBoundary -/

#print axioms InfoGeometry.Krein.KreinAdjointBoundary.kreinGram_eq_zero_iff
#print axioms InfoGeometry.Krein.KreinAdjointBoundary.kreinAdjoint_eq_adjoint_iff
#print axioms InfoGeometry.Krein.KreinAdjointBoundary.hilbert_skew_iff_commutes
#print axioms InfoGeometry.Krein.KreinAdjointBoundary.kreinGram_eq_zero_iff_of_commutes
#print axioms InfoGeometry.Krein.KreinAdjointBoundary.diagonalProjector_idempotent
#print axioms InfoGeometry.Krein.KreinAdjointBoundary.diagonalProjector_fst_eq_snd
#print axioms InfoGeometry.Krein.KreinAdjointBoundary.diagonalProjector_fixes_diagonal
#print axioms InfoGeometry.Krein.KreinAdjointBoundary.diagonalProjector_kreinGram
#print axioms InfoGeometry.Krein.KreinAdjointBoundary.diagonalProjector_ne_zero
#print axioms InfoGeometry.Krein.KreinAdjointBoundary.diagonalProjector_not_kreinSelfAdjoint
#print axioms InfoGeometry.Krein.KreinAdjointBoundary.diagonalProjector_hilbertGram_ne_zero

/-! ## InfoGeometry.Krein.DoubledKreinWitnesses -/

#print axioms InfoGeometry.Krein.DoubledKreinWitnesses.upperTransfer_sq
#print axioms InfoGeometry.Krein.DoubledKreinWitnesses.lowerTransfer_sq
#print axioms InfoGeometry.Krein.DoubledKreinWitnesses.upperTransfer_adjoint
#print axioms InfoGeometry.Krein.DoubledKreinWitnesses.lowerTransfer_adjoint
#print axioms InfoGeometry.Krein.DoubledKreinWitnesses.upperTransfer_kreinAdjoint
#print axioms InfoGeometry.Krein.DoubledKreinWitnesses.lowerTransfer_kreinAdjoint
#print axioms InfoGeometry.Krein.DoubledKreinWitnesses.upperTransfer_kreinGram
#print axioms InfoGeometry.Krein.DoubledKreinWitnesses.lowerTransfer_kreinGram
#print axioms InfoGeometry.Krein.DoubledKreinWitnesses.upperTransfer_kreinGram_apply
#print axioms InfoGeometry.Krein.DoubledKreinWitnesses.lowerTransfer_kreinGram_apply
#print axioms InfoGeometry.Krein.DoubledKreinWitnesses.upperTransfer_hilbert_expectation
#print axioms InfoGeometry.Krein.DoubledKreinWitnesses.upperTransfer_krein_expectation
#print axioms InfoGeometry.Krein.DoubledKreinWitnesses.lowerTransfer_hilbert_expectation
#print axioms InfoGeometry.Krein.DoubledKreinWitnesses.lowerTransfer_krein_expectation
#print axioms InfoGeometry.Krein.DoubledKreinWitnesses.upperTransfer_opposite_expectation_signs
#print axioms InfoGeometry.Krein.DoubledKreinWitnesses.lowerTransfer_negative_krein_expectation
#print axioms InfoGeometry.Krein.DoubledKreinWitnesses.transfers_not_commute
#print axioms InfoGeometry.Krein.DoubledKreinWitnesses.complex_i_kreinSelfAdjoint
#print axioms InfoGeometry.Krein.DoubledKreinWitnesses.eq_zero_of_sq_neg_id_eigenvector
#print axioms InfoGeometry.Krein.DoubledKreinWitnesses.complex_i_no_real_eigenvector

/-! ## InfoGeometry.Order.KreinOctonionDependencyPoset -/

#print axioms InfoGeometry.KreinOctonionDependencyPoset.card_node
#print axioms InfoGeometry.KreinOctonionDependencyPoset.edge_iff_covBy
#print axioms InfoGeometry.KreinOctonionDependencyPoset.edge_eq_covBy
#print axioms InfoGeometry.KreinOctonionDependencyPoset.le_iff_reachable
#print axioms InfoGeometry.KreinOctonionDependencyPoset.reachable_iff_lt
#print axioms InfoGeometry.KreinOctonionDependencyPoset.level_strictMono
#print axioms InfoGeometry.KreinOctonionDependencyPoset.level_lt_of_reachable
#print axioms InfoGeometry.KreinOctonionDependencyPoset.reachable_irrefl
#print axioms InfoGeometry.KreinOctonionDependencyPoset.reachable_asymm
#print axioms InfoGeometry.KreinOctonionDependencyPoset.predecessors_incomparable
#print axioms InfoGeometry.KreinOctonionDependencyPoset.cut_reaches
#print axioms InfoGeometry.KreinOctonionDependencyPoset.reaches_synthesis
#print axioms InfoGeometry.KreinOctonionDependencyPoset.calibration_quantization_isLUB
#print axioms InfoGeometry.KreinOctonionDependencyPoset.thesis_shadow_no_isLUB
#print axioms InfoGeometry.KreinOctonionDependencyPoset.no_cover_rank

/-! ## Existing native Zorn left-action owners -/

#print axioms InfoGeometry.Algebra.ZornLeftCAR.leftMultiplication_injective
#print axioms InfoGeometry.Algebra.ZornLeftCAR.leftMultiplication_square
#print axioms InfoGeometry.Algebra.ZornLeftCAR.leftMultiplication_anticommutator
#print axioms InfoGeometry.Algebra.ZornLeftCAR.leftMultiplication_not_multiplicative
#print axioms InfoGeometry.Algebra.ZornLeftCAR.multiplicationDefect_apply
#print axioms InfoGeometry.Algebra.ZornLeftCAR.multiplicationDefect_one
#print axioms InfoGeometry.Algebra.ZornLeftCAR.nonzero_multiplicationDefect_not_mem_left_range
#print axioms InfoGeometry.Algebra.ZornLeftCAR.multiplicationDefect_swap
#print axioms InfoGeometry.Algebra.ZornLeftCAR.leftMultiplication_mul_eq_iff
#print axioms InfoGeometry.Algebra.ZornLeftCAR.leftMultiplication_commutator_defect
#print axioms InfoGeometry.Algebra.ZornLeftCAR.multiplicationDefect_eq_half_commutator_correction
#print axioms InfoGeometry.Algebra.ZornLeftCAR.multiplicationDefect_mem_native_lieSpan
#print axioms InfoGeometry.Algebra.ZornLeftCAR.multiplicationDefect_U01_ne_zero
#print axioms InfoGeometry.Algebra.ZornLeftCAR.left_action_range_lt_native_lieSpan

/-! ## Existing doubled-space generator owners -/

#print axioms InfoGeometry.Krein.complex_i_sq
#print axioms InfoGeometry.Krein.modular_j_involution
#print axioms InfoGeometry.Krein.modular_j_kreinSkewAdjoint
