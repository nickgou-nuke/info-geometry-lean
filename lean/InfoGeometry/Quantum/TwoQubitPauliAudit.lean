/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Quantum.TwoQubitPauliBasis
import InfoGeometry.Quantum.TwoQubitPauliPhase

/-!
# Axiom audit for binary projective incidence and its signed matrix lifts

This companion prints the transitive axiom dependencies of every public
named declaration in the five source owners, including changes of real phase
convention. It is checked with the same pinned Lean and Mathlib versions.
-/

-- BinaryWeyl.lean
#print axioms InfoGeometry.Quantum.BinaryWeyl.shift
#print axioms InfoGeometry.Quantum.BinaryWeyl.clock
#print axioms InfoGeometry.Quantum.BinaryWeyl.phase
#print axioms InfoGeometry.Quantum.BinaryWeyl.phase_zero
#print axioms InfoGeometry.Quantum.BinaryWeyl.phase_one
#print axioms InfoGeometry.Quantum.BinaryWeyl.phase_add
#print axioms InfoGeometry.Quantum.BinaryWeyl.phase_mul_self
#print axioms InfoGeometry.Quantum.BinaryWeyl.phase_ne_zero
#print axioms InfoGeometry.Quantum.BinaryWeyl.phase_injective
#print axioms InfoGeometry.Quantum.BinaryWeyl.word
#print axioms InfoGeometry.Quantum.BinaryWeyl.word_zero_zero
#print axioms InfoGeometry.Quantum.BinaryWeyl.word_mul
#print axioms InfoGeometry.Quantum.BinaryWeyl.word_transpose_eq_reverse
#print axioms InfoGeometry.Quantum.BinaryWeyl.word_transpose
#print axioms InfoGeometry.Quantum.BinaryWeyl.word_trace_pair
#print axioms InfoGeometry.Quantum.BinaryWeyl.shift_clock_noncommute

-- BinarySymplecticGeometry.lean
#print axioms InfoGeometry.Projective.BinarySymplectic.Bit
#print axioms InfoGeometry.Projective.BinarySymplectic.Label
#print axioms InfoGeometry.Projective.BinarySymplectic.finrank_label
#print axioms InfoGeometry.Projective.BinarySymplectic.bit_eq_zero_or_one
#print axioms InfoGeometry.Projective.BinarySymplectic.projectivization_mk_eq_iff
#print axioms InfoGeometry.Projective.BinarySymplectic.projectivePointEquiv
#print axioms InfoGeometry.Projective.BinarySymplectic.projectivePointEquiv_apply
#print axioms InfoGeometry.Projective.BinarySymplectic.projectivization_card
#print axioms InfoGeometry.Projective.BinarySymplectic.cocycle
#print axioms InfoGeometry.Projective.BinarySymplectic.symplectic
#print axioms InfoGeometry.Projective.BinarySymplectic.label_add_self
#print axioms InfoGeometry.Projective.BinarySymplectic.label_add_add_left
#print axioms InfoGeometry.Projective.BinarySymplectic.label_add_add_right
#print axioms InfoGeometry.Projective.BinarySymplectic.cocycle_zero_left
#print axioms InfoGeometry.Projective.BinarySymplectic.cocycle_zero_right
#print axioms InfoGeometry.Projective.BinarySymplectic.cocycle_add_left
#print axioms InfoGeometry.Projective.BinarySymplectic.cocycle_add_right
#print axioms InfoGeometry.Projective.BinarySymplectic.cocycle_assoc
#print axioms InfoGeometry.Projective.BinarySymplectic.symplectic_comm
#print axioms InfoGeometry.Projective.BinarySymplectic.symplectic_self
#print axioms InfoGeometry.Projective.BinarySymplectic.symplectic_zero_left
#print axioms InfoGeometry.Projective.BinarySymplectic.symplectic_zero_right
#print axioms InfoGeometry.Projective.BinarySymplectic.symplectic_add_left
#print axioms InfoGeometry.Projective.BinarySymplectic.symplectic_add_right
#print axioms InfoGeometry.Projective.BinarySymplectic.symplectic_left_add
#print axioms InfoGeometry.Projective.BinarySymplectic.symplectic_right_add
#print axioms InfoGeometry.Projective.BinarySymplectic.quadraticPhase
#print axioms InfoGeometry.Projective.BinarySymplectic.quadraticPhase_zero
#print axioms InfoGeometry.Projective.BinarySymplectic.quadraticPhase_add
#print axioms InfoGeometry.Projective.BinarySymplectic.rephasedCocycle
#print axioms InfoGeometry.Projective.BinarySymplectic.rephasedCocycle_zero_left
#print axioms InfoGeometry.Projective.BinarySymplectic.rephasedCocycle_zero_right
#print axioms InfoGeometry.Projective.BinarySymplectic.rephasedCocycle_assoc
#print axioms InfoGeometry.Projective.BinarySymplectic.rephasedCocycle_symplectic
#print axioms InfoGeometry.Projective.BinarySymplectic.rephasedCocycle_self
#print axioms InfoGeometry.Projective.BinarySymplectic.rephasedCocycle_quadraticPhase
#print axioms InfoGeometry.Projective.BinarySymplectic.symplectic_nondegenerate
#print axioms InfoGeometry.Projective.BinarySymplectic.points
#print axioms InfoGeometry.Projective.BinarySymplectic.mem_points
#print axioms InfoGeometry.Projective.BinarySymplectic.line
#print axioms InfoGeometry.Projective.BinarySymplectic.mem_line
#print axioms InfoGeometry.Projective.BinarySymplectic.line_swap
#print axioms InfoGeometry.Projective.BinarySymplectic.line_add_right
#print axioms InfoGeometry.Projective.BinarySymplectic.line_add_left
#print axioms InfoGeometry.Projective.BinarySymplectic.add_ne_zero_of_ne
#print axioms InfoGeometry.Projective.BinarySymplectic.left_ne_add
#print axioms InfoGeometry.Projective.BinarySymplectic.right_ne_add
#print axioms InfoGeometry.Projective.BinarySymplectic.line_card
#print axioms InfoGeometry.Projective.BinarySymplectic.line_subset_points
#print axioms InfoGeometry.Projective.BinarySymplectic.mem_span_pair_iff
#print axioms InfoGeometry.Projective.BinarySymplectic.mem_line_iff_mem_span_pair
#print axioms InfoGeometry.Projective.BinarySymplectic.finrank_span_pair
#print axioms InfoGeometry.Projective.BinarySymplectic.line_eq_of_mem
#print axioms InfoGeometry.Projective.BinarySymplectic.symplectic_eq_of_distinct_mem_line
#print axioms InfoGeometry.Projective.BinarySymplectic.lines
#print axioms InfoGeometry.Projective.BinarySymplectic.mem_lines_iff
#print axioms InfoGeometry.Projective.BinarySymplectic.line_mem_lines
#print axioms InfoGeometry.Projective.BinarySymplectic.card_of_mem_lines
#print axioms InfoGeometry.Projective.BinarySymplectic.exists_unique_line
#print axioms InfoGeometry.Projective.BinarySymplectic.line_isotropic_iff
#print axioms InfoGeometry.Projective.BinarySymplectic.commutingLines
#print axioms InfoGeometry.Projective.BinarySymplectic.commutingLines_subset_lines
#print axioms InfoGeometry.Projective.BinarySymplectic.line_mem_commutingLines_iff
#print axioms InfoGeometry.Projective.BinarySymplectic.points_card
#print axioms InfoGeometry.Projective.BinarySymplectic.lines_card
#print axioms InfoGeometry.Projective.BinarySymplectic.commutingLines_card
#print axioms InfoGeometry.Projective.BinarySymplectic.noncommutingLines_card

-- TwoQubitPauliGeometry.lean
#print axioms InfoGeometry.Quantum.TwoQubitPauli.Operator
#print axioms InfoGeometry.Quantum.TwoQubitPauli.pauli
#print axioms InfoGeometry.Quantum.TwoQubitPauli.pauli_zero
#print axioms InfoGeometry.Quantum.TwoQubitPauli.pauli_mul
#print axioms InfoGeometry.Quantum.TwoQubitPauli.pauli_mul_self
#print axioms InfoGeometry.Quantum.TwoQubitPauli.pauli_mul_inverse
#print axioms InfoGeometry.Quantum.TwoQubitPauli.pauli_ne_zero
#print axioms InfoGeometry.Quantum.TwoQubitPauli.smul_pauli_injective
#print axioms InfoGeometry.Quantum.TwoQubitPauli.pauli_phase_commutation
#print axioms InfoGeometry.Quantum.TwoQubitPauli.pauli_lie
#print axioms InfoGeometry.Quantum.TwoQubitPauli.pauli_line_product
#print axioms InfoGeometry.Quantum.TwoQubitPauli.pauli_commute_iff
#print axioms InfoGeometry.Quantum.TwoQubitPauli.pauli_anticommute_of_pairing_one
#print axioms InfoGeometry.Quantum.TwoQubitPauli.line_pairwise_commute_iff
#print axioms InfoGeometry.Quantum.TwoQubitPauli.commuting_operator_lines_card
#print axioms InfoGeometry.Quantum.TwoQubitPauli.first_factor_noncommute

-- TwoQubitPauliBasis.lean
#print axioms InfoGeometry.Quantum.TwoQubitPauli.pauli_trace_pair
#print axioms InfoGeometry.Quantum.TwoQubitPauli.pauli_trace
#print axioms InfoGeometry.Quantum.TwoQubitPauli.pauli_linearIndependent
#print axioms InfoGeometry.Quantum.TwoQubitPauli.pauliBasis
#print axioms InfoGeometry.Quantum.TwoQubitPauli.pauliBasis_apply
#print axioms InfoGeometry.Quantum.TwoQubitPauli.trace_eq_identity_coefficient
#print axioms InfoGeometry.Quantum.TwoQubitPauli.trace_zero_iff_identity_coefficient_zero
#print axioms InfoGeometry.Quantum.TwoQubitPauli.nonzero_pauli_span_eq_sl
#print axioms InfoGeometry.Quantum.TwoQubitPauli.nonzero_pauli_span_finrank

-- TwoQubitPauliPhase.lean
#print axioms InfoGeometry.Quantum.TwoQubitPauli.rephasedPauli
#print axioms InfoGeometry.Quantum.TwoQubitPauli.rephasedPauli_zero
#print axioms InfoGeometry.Quantum.TwoQubitPauli.rephasedPauli_zero_of_normalized
#print axioms InfoGeometry.Quantum.TwoQubitPauli.phase_smul_rephasedPauli
#print axioms InfoGeometry.Quantum.TwoQubitPauli.smul_rephasedPauli_injective
#print axioms InfoGeometry.Quantum.TwoQubitPauli.rephasedPauli_mul
#print axioms InfoGeometry.Quantum.TwoQubitPauli.rephasedPauli_mul_self
#print axioms InfoGeometry.Quantum.TwoQubitPauli.rephasedPauli_phase_commutation
#print axioms InfoGeometry.Quantum.TwoQubitPauli.rephasedPauli_commute_iff
#print axioms InfoGeometry.Quantum.TwoQubitPauli.rephasedPauli_first_factor_noncommute
#print axioms InfoGeometry.Quantum.TwoQubitPauli.not_rephasedPauli_symplectic_product
#print axioms InfoGeometry.Quantum.TwoQubitPauli.pauli_transpose
#print axioms InfoGeometry.Quantum.TwoQubitPauli.rephasedPauli_transpose
#print axioms InfoGeometry.Quantum.TwoQubitPauli.rephasedPauli_isSymm_iff
#print axioms InfoGeometry.Quantum.TwoQubitPauli.rephasedPauli_isHermitian_iff
#print axioms InfoGeometry.Quantum.TwoQubitPauli.rephasedPauli_xz_not_isSymm
#print axioms InfoGeometry.Quantum.TwoQubitPauli.quadraticPauli_mul
#print axioms InfoGeometry.Quantum.TwoQubitPauli.quadraticPauli_eq_transpose
#print axioms InfoGeometry.Quantum.TwoQubitPauli.quadraticPauli_eq_reverse
#print axioms InfoGeometry.Quantum.TwoQubitPauli.pauli_mul_quadraticPauli
#print axioms InfoGeometry.Quantum.TwoQubitPauli.quadraticPauli_mul_pauli
#print axioms InfoGeometry.Quantum.TwoQubitPauli.quadraticPauli_xz_square
#print axioms InfoGeometry.Quantum.TwoQubitPauli.quadraticPauli_xz_product_ne_symplectic
