import InfoGeometry.QuantumContext.CausalPetzStiefelConservation

/-!
# Audit Companion for Causal Petz Stiefel Conservation Law

Module: `InfoGeometry.QuantumContext.CausalPetzStiefelConservationAudit`

This module audits the axiomatic footprint of all theorems in
`CausalPetzStiefelConservation.lean`.
-/

namespace InfoGeometry.QuantumContext.CausalPetz.Audit

open InfoGeometry.QuantumContext.CausalPetz

#print axioms InfoGeometry.OperatorAlgebra.FiniteMatrixNoncommutativeWitness.matrix_units_noncommute

-- Section 1: Gram Partial Isometry Constraint
#print axioms blockIntertwiner_gram
#print axioms gram_isometry_iff_stiefel

-- Section 2: Trace Conservation Law & Zero-Sum Trade-Off
#print axioms petz_trace_preservation
#print axioms past_preservation_forces_future_quiescence
#print axioms future_dominance_forces_past_annihilation

-- Section 3: Master Verification Certificate
#print axioms compile_causal_petz_stiefel

end InfoGeometry.QuantumContext.CausalPetz.Audit
