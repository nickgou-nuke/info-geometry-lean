import InfoGeometry.QuantumContext.GraphHodgeDiracColimit

/-!
# Axiomatic Audit for Graph Hodge-Dirac Colimit and Casimir Stabilization

Module: `InfoGeometry.QuantumContext.GraphHodgeDiracColimitAudit`

This module audits the axiomatic footprint of all theorems in
`GraphHodgeDiracColimit.lean`.
-/

namespace InfoGeometry.QuantumContext.GraphHodgeDiracColimit.Audit

open InfoGeometry.QuantumContext.GraphHodgeDiracColimit

-- Section 1: Finite Graph Complex & Discrete Hodge-Dirac Operator
#print axioms laplacian_trace_eq
#print axioms graphDirac_sq
#print axioms chiralGamma_sq
#print axioms graphDirac_anticomm_gamma
#print axioms graphDirac_comm_sq

-- Section 2: Block Trace & Orthogonal Direct Sums
#print axioms trace_fromBlocks
#print axioms nodeLaplacian_directSum
#print axioms edgeLaplacian_directSum
#print axioms trace_nodeLaplacian_directSum
#print axioms trace_edgeLaplacian_directSum

-- Section 3: Inductive Extension of Graphs & Casimir Trace Stabilization
#print axioms nodeLaplacian_extendGraphZero
#print axioms edgeLaplacian_extendGraphZero
#print axioms trace_nodeLaplacian_invariant
#print axioms trace_edgeLaplacian_invariant

-- Section 4: Higher Casimir Powers and Trace Stabilization
#print axioms nodeLaplacian_sq_extend
#print axioms trace_nodeLaplacian_sq_invariant
#print axioms edgeLaplacian_sq_extend
#print axioms trace_edgeLaplacian_sq_invariant
#print axioms nodeLaplacian_pow_extend
#print axioms trace_nodeLaplacian_pow_invariant
#print axioms edgeLaplacian_pow_extend
#print axioms trace_edgeLaplacian_pow_invariant

-- Section 5: Inductive Sequence Colimit Stabilization
#print axioms trace_nodeLaplacian_extendChain
#print axioms trace_edgeLaplacian_extendChain
#print axioms trace_nodeLaplacian_sq_extendChain
#print axioms trace_edgeLaplacian_sq_extendChain
#print axioms trace_nodeLaplacian_pow_extendChain
#print axioms trace_edgeLaplacian_pow_extendChain
#print axioms colimit_dirac_sq
#print axioms colimit_dirac_comm_laplacian
#print axioms colimit_chiral_involution
#print axioms colimit_dirac_anticomm_chiral

-- Section 6: Master Verification Certificate
#print axioms compile_graph_hodge_dirac_colimit

end InfoGeometry.QuantumContext.GraphHodgeDiracColimit.Audit
