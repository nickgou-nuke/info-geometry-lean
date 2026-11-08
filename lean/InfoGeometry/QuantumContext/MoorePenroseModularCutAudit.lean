/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.MoorePenroseModularCut

/-!
# Audit: Finite Diagonal Moore–Penrose Support Cut

Independent audit verifying that all 20 theorems in
`InfoGeometry.QuantumContext.MoorePenroseModularCut` depend strictly on standard
Core Lean 4 / Mathlib axioms (`[propext, Classical.choice, Quot.sound]`) with zero
`sorry`, zero `admit`, zero custom axioms, and zero `Prop`-bundling wrappers.
-/

namespace InfoGeometry.QuantumContext.MoorePenroseAudit

open InfoGeometry.QuantumContext.MoorePenrose

#print axioms penrose_one
#print axioms penrose_two
#print axioms mul_pinv_eq_support
#print axioms pinv_mul_eq_support
#print axioms support_idempotent
#print axioms eviction_idempotent
#print axioms support_add_eviction
#print axioms support_mul_eviction
#print axioms pinv_annihilates_eviction
#print axioms eviction_annihilates_density
#print axioms supportwise_scalar_inverse_identity
#print axioms active_support_anchor
#print axioms densityMatrix_penrose_one
#print axioms pinvMatrix_penrose_two
#print axioms pinvMatrix_mul_densityMatrix
#print axioms densityMatrix_mul_pinvMatrix
#print axioms supportMatrix_add_evictionMatrix
#print axioms supportMatrix_mul_evictionMatrix
#print axioms matrix_reduced_trace_identity
#print axioms matrix_reduced_trace_identity_of_right_supported

end InfoGeometry.QuantumContext.MoorePenroseAudit
