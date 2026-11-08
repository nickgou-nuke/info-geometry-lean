import InfoGeometry.Canonical.BdGTopologicalSuperconductor

/-!
# Audit Companion for BdG Topological Superconductor Complete Module

Module: `InfoGeometry.Canonical.BdGTopologicalSuperconductorAudit`

This module audits the axiomatic footprint of all theorems in
`BdGTopologicalSuperconductor.lean`.
-/

namespace InfoGeometry.Canonical.BdGTopologicalSuperconductor.Audit

open InfoGeometry.Canonical.BdGTopologicalSuperconductor

-- Section 1: The Physical BdG Operator in Nambu Basis
#print axioms trace_fromBlocks
#print axioms bdgOp_trace
#print axioms bdgOp_trace_self_zero

-- Section 2: Particle-Hole Symmetry Operator & Andreev Reversal
#print axioms particleHoleTau1_sq
#print axioms particleHole_swap
#print axioms bdg_particleHole_antisymm
#print axioms bdg_particleHole_inversion

-- Section 3: Andreev Boundary Reflection S-Matrix
#print axioms andreevSMatrix_transpose
#print axioms andreevSMatrix_sq
#print axioms andreevSMatrix_orthogonal

-- Section 4: Schur Complement & Bandgap Factorization
#print axioms schur_factorization

-- Section 5: Majorana Zero-Mode Criterion
#print axioms zero_mode_particle_hole_compatible

-- Section 6: Master Verification Certificate
#print axioms compile_bdg_topological_superconductor_complete

end InfoGeometry.Canonical.BdGTopologicalSuperconductor.Audit
