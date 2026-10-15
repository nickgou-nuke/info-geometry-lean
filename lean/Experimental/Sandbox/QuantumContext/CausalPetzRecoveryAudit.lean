import Experimental.Sandbox.QuantumContext.CausalPetzRecovery

/-!
# Audit Companion for Causal Petz Recovery Map

This module audits the axiomatic footprint of all theorems in
`CausalPetzRecovery.lean`.
-/

namespace InfoGeometry.Experimental.CausalPetz.Audit

open InfoGeometry.Experimental.CausalPetz

#print axioms standardCausalProjectorSystem
#print axioms standardCausalProjectorSystem_projectors_nonzero
#print axioms matrix_units_noncommutative
#print axioms InfoGeometry.OperatorAlgebra.FiniteMatrixNoncommutativeWitness.matrix_units_noncommute_of_nontrivial

-- Section 1
#print axioms triangular_rank_formula
#print axioms causal_channel_idempotent
#print axioms causal_channel_annihilates_acausal
#print axioms causal_state_supported_on_pi

-- Section 2
#print axioms pinv_mul_pi_eq_self
#print axioms pi_mul_pinv_eq_self
#print axioms petz_gram_operator_identity

-- Section 3
#print axioms petz_block_past
#print axioms petz_block_coherence_PQ
#print axioms petz_block_coherence_QP
#print axioms petz_block_future
#print axioms petz_block_reconstruct_matrix

-- Section 4
#print axioms petz_decoupled_future_zero
#print axioms petz_past_exact_preservation
#print axioms petz_future_nonvanishing

-- Section 5
#print axioms petz_reconstructs_reference

-- Section 6
#print axioms compile_causal_petz_recovery

end InfoGeometry.Experimental.CausalPetz.Audit
