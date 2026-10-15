import Experimental.Sandbox.SuperGrassmannian.CategoricalModuleColimitSato

/-!
# Audit Companion: Categorical Graded Module Inductive Colimit & The Sato Infinite Grassmannian

Module: `Experimental.Sandbox.SuperGrassmannian.CategoricalModuleColimitSatoAudit`

This module audits the axiomatic footprint of all theorems in `CategoricalModuleColimitSato.lean`.
-/

namespace InfoGeometry.SuperGrassmannian.ModuleColimitSato.Audit

open InfoGeometry.SuperGrassmannian.ModuleColimitSato

-- Section 1: Graded Module Inductive Sequence
#print axioms gamma_comp_self
#print axioms grade_intertwining_comp
#print axioms grade_intertwining_chain
#print axioms chiral_projector_sum
#print axioms chiral_projector_diff
#print axioms grade_intertwining_projectors

-- Section 2: Graded Module Action Intertwining
#print axioms action_intertwining_chain

-- Section 3: The Sato Infinite Grassmannian Limit
#print axioms sato_virtual_index_invariant
#print axioms sato_virtual_index_chain_invariant
#print axioms vacuum_sato_index_zero

-- Section 4: Normalized Type II_1 Colimit Module State
#print axioms normalized_module_identity_trace_eq_one
#print axioms colimit_module_trace_invariant
#print axioms colimit_module_trace_chain_invariant

-- Section 5: Master Verification Certificate
#print axioms compile_categorical_module_colimit_sato

end InfoGeometry.SuperGrassmannian.ModuleColimitSato.Audit
