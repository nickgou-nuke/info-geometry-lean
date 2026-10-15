import Experimental.Sandbox.QuantumContext.DiscreteKreinAndreevGraphEngine

/-!
# Audit Companion for Discrete Krein-Andreev Graph Engine

Module: `Experimental.Sandbox.QuantumContext.DiscreteKreinAndreevGraphEngineAudit`

This module audits the axiomatic footprint of all theorems in
`DiscreteKreinAndreevGraphEngine.lean`.
-/

namespace Experimental.Sandbox.QuantumContext.DiscreteKreinAndreevGraphEngine.Audit

open Experimental.Sandbox.QuantumContext.DiscreteKreinAndreevGraphEngine

-- Section 1: The Discrete Exterior Complex & Hodge-Dirac Operator
#print axioms laplacian_trace_eq
#print axioms hodgeDirac_sq

-- Section 2: Chiral Grading & Krein Fundamental Symmetry
#print axioms chiralGamma_sq
#print axioms dirac_anticomm_gamma
#print axioms kreinJ_sq
#print axioms kreinJ_anticomm_gamma
#print axioms kreinDirac_formula
#print axioms kreinDirac_sq_formula

-- Section 3: The Andreev Reflection & Bogoliubov-de Gennes (BdG) Symmetries
#print axioms andreevTau1_sq
#print axioms andreev_swap
#print axioms andreev_bdg_swap
#print axioms andreev_bdg_antisymmetry
#print axioms bdgHamiltonian_transpose
#print axioms andreev_skew_pairing_reversal

-- Section 4: Genuine Matrix Moore-Penrose & Drazin Sieve Projectors (Resolving Trap T16)
#print axioms matrix_support_proj_idempotent
#print axioms matrix_kernel_annihilates_density
#print axioms matrix_kernel_proj_idempotent
#print axioms drazin_core_idempotent
#print axioms drazin_stationary_sink_idempotent
#print axioms drazin_stationary_sink_annihilates_generator
#print axioms drazin_stationary_sink_annihilates_generator_left

-- Section 5: Master Verification Certificate
#print axioms compile_discrete_krein_andreev_graph_engine

end Experimental.Sandbox.QuantumContext.DiscreteKreinAndreevGraphEngine.Audit
