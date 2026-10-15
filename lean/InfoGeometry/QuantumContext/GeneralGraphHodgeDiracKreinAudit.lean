import InfoGeometry.QuantumContext.GeneralGraphHodgeDiracKrein

/-!
# Audit Companion for General Graph Hodge-Dirac Operator and Krein Chiral Split

Module: `InfoGeometry.QuantumContext.GeneralGraphHodgeDiracKreinAudit`

This module audits the axiomatic footprint of all theorems in
`GeneralGraphHodgeDiracKrein.lean`.
-/

namespace InfoGeometry.QuantumContext.GeneralGraphHodgeDiracKrein.Audit

open InfoGeometry.QuantumContext.GeneralGraphHodgeDiracKrein

-- Section 1: The Discrete Exterior Derivative & Codifferential on Graphs
#print axioms laplacian_trace_eq

-- Section 2: The Discrete Hodge-Dirac Operator on Graded Forms
#print axioms graphDirac_sq

-- Section 3: The Chiral Grading Operator (Fermion Parity)
#print axioms graphChiralGamma_sq
#print axioms graphDirac_anticomm_gamma

-- Section 4: Krein CPT Involution J and Krein-Chiral Dirac Operator
#print axioms graphKreinJ_sq
#print axioms graphKreinJ_anticomm_gamma
#print axioms graphKreinDirac_formula

-- Section 5: The Projector Sieve Algebra
#print axioms nullProjector_sq
#print axioms nullProjector_annihilate
#print axioms drazinCore_sq
#print axioms drazinKernel_annihilates_L

-- Section 6: Master Verification Certificate
#print axioms compile_general_graph_hodge_dirac_krein

end InfoGeometry.QuantumContext.GeneralGraphHodgeDiracKrein.Audit
