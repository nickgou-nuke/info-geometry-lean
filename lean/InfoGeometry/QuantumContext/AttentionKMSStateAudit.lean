/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.QuantumContext.AttentionKMSState

/-!
# Audit Companion: Finite Softmax State, GNS Bridge & Reduced Pruned Trace Identity

This module audits the foundational axioms and kernel dependency manifest of all
theorem declarations in `InfoGeometry.QuantumContext.AttentionKMSState`.
-/

open InfoGeometry.QuantumContext.AttentionKMSState

#print axioms softmaxWeight_pos
#print axioms softmaxWeight_sum_one
#print axioms attentionDensityMatrix_trace_one
#print axioms attentionState_eq_gnsInner_cyclic
#print axioms attentionState_quadratic_eq_gnsInner
#print axioms attentionState_eq_sum
#print axioms attentionState_quadratic_eq_sum
#print axioms attentionState_quadratic_nonneg
#print axioms attentionState_faithful
#print axioms attention_kms_condition
#print axioms attentionDensityMatrixInv_mul
#print axioms attentionDensityMatrix_mul_inv
#print axioms attentionState_kms
#print axioms modularConjugation_involutive
#print axioms modularConjugation_mul
#print axioms modularConjugation_one
#print axioms attentionTomitaJ_involutive
#print axioms attentionTomitaJ_mul
#print axioms attention_tomita_duality
#print axioms prunedState_quadratic_eq_gnsInner
#print axioms prunedState_null_iff_active_columns_zero
#print axioms prunedState_null_iff_right_support_annihilation
#print axioms prunedState_null_mul_left
#print axioms prunedState_diagonal
#print axioms projectionMatrix_ne_zero
#print axioms projectionMatrix_transpose
#print axioms projectionMatrix_mul_self
#print axioms pruned_cache_has_nontrivial_null_ideal
#print axioms sink_anchor_separating
#print axioms prunedDensityMatrixPinv_mul_eq_projector
#print axioms prunedDensityMatrixPinv_isMoorePenroseInverse
#print axioms prunedState_reduced_trace_identity
#print axioms prunedState_reduced_trace_identity_of_right_supported
