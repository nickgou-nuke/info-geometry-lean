/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.QuantumContext.AttentionKMSState

/-!
# Audit Companion: Attention KMS State and GNS Representation

This module audits the foundational axioms and kernel dependency manifest
of `InfoGeometry.QuantumContext.AttentionKMSState`.
-/

open InfoGeometry.QuantumContext.AttentionKMSState

#print axioms softmaxWeight_pos
#print axioms softmaxWeight_sum_one
#print axioms attentionDensityMatrix_trace_one
#print axioms attentionState_eq_sum
#print axioms attentionState_quadratic_eq_sum
#print axioms attentionState_quadratic_nonneg
#print axioms attentionState_faithful
#print axioms attention_kms_condition
#print axioms attentionDensityMatrixInv_mul
#print axioms attentionState_kms
#print axioms modularConjugation_involutive
#print axioms modularConjugation_mul
#print axioms pruned_cache_has_nontrivial_null_ideal
#print axioms sink_anchor_separating
#print axioms compile_attention_kms_state
