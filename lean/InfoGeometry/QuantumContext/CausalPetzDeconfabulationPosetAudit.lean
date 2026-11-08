import InfoGeometry.QuantumContext.CausalPetzDeconfabulationPoset

/-!
# Audit Companion for Causal Petz Deconfabulation Poset

This module audits the axiomatic footprint of all theorems in
`CausalPetzDeconfabulationPoset.lean`.
-/

namespace InfoGeometry.QuantumContext.CausalPetzDeconfabulationPoset.Audit

open InfoGeometry.QuantumContext.CausalPetzDeconfabulationPoset

#print axioms standardCausalProjectorSystem
#print axioms standardCausalProjectorSystem_projectors_nonzero
#print axioms InfoGeometry.OperatorAlgebra.FiniteMatrixNoncommutativeWitness.matrix_units_noncommute
#print axioms InfoGeometry.OperatorAlgebra.FiniteMatrixNoncommutativeWitness.matrix_units_noncommute_of_nontrivial

-- Poset and Prerequisite Architecture
#print axioms prerequisites_injective
#print axioms a1_precedes_all
#print axioms a1_le_a2
#print axioms a2_le_a3
#print axioms a3_le_a4
#print axioms a4_le_a5
#print axioms a5_le_a6
#print axioms strict_causal_chain

-- 𝒜₁: Kinematics & Triangular Filtration
#print axioms triangular_rank_formula

-- 𝒜₂: Causal Pinching Channel & Acausal Annihilation
#print axioms causal_channel_idempotent
#print axioms causal_channel_annihilates_acausal
#print axioms causal_channel_preserves_supported

-- 𝒜₃: Petz Intertwiner & Gram Partial Isometry
#print axioms pinv_mul_pi_eq_self
#print axioms pi_mul_pinv_eq_self
#print axioms petz_gram_operator_identity

-- 𝒜₄: Past-Future 2x2 Block Splitting & Transfer Operators
#print axioms blockIntertwiner_gram
#print axioms gram_isometry_iff_stiefel
#print axioms stiefel_tradeoff
#print axioms past_normalization_forces_future_zero

-- 𝒜₅: Retrocausal Reconstruction Matrix
#print axioms petz_block_past
#print axioms petz_block_coherence_PQ
#print axioms petz_block_coherence_QP
#print axioms petz_block_future
#print axioms petz_block_reconstruct_matrix
#print axioms petz_block_trace
#print axioms petz_block_trace_preservation_on_support
#print axioms petz_block_coherence_cauchy_schwarz
#print axioms petz_decoupled_future_zero
#print axioms petz_past_exact_preservation

-- 𝒜₆: Quantum Markov Sufficiency & Relative Modular Flow
#print axioms relativeModularOperator_intertwines_causal_compression
#print axioms relativeModularOperator_preserves_causal_observables

-- Epistemic Deconfabulation & Quadratic Response
#print axioms deconfabulateMap_monotone
#print axioms stiefel_coherence_is_quadratic_response
#print axioms stiefel_coherence_optimal_activity

-- Master Certificate
#print axioms compile_causal_petz_deconfabulation

end InfoGeometry.QuantumContext.CausalPetzDeconfabulationPoset.Audit
