/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Synthesis.TransactionalQueryKeyRoPEPhaseSpaceBridge

/-!
# Audit: `TransactionalQueryKeyRoPEPhaseSpaceBridge`

Typecheck and signature audit for `InfoGeometry.Synthesis.TransactionalQueryKeyRoPEPhaseSpaceBridge`.
-/

namespace InfoGeometry.Synthesis.TransactionalQueryKeyRoPEPhaseSpaceBridge.Audit

open InfoGeometry.Synthesis.TransactionalQueryKeyRoPEPhaseSpaceBridge

#check @featureInner
#check @transactionalLogitMatrix
#check @causalValueOutput
#check @causalValueOutput_kv_cache_prefix_invariance
#check @transactionalLogitMatrix_row_depends_only_on_instant_query
#check @forwardKeyContraction
#check @backwardKeyGradient
#check @forward_backward_query_key_gradient_duality
#check @backwardKeyGradient_depends_only_on_future_queries
#check @forward_backward_doubleKrein_selfAdjoint
#check @rope_mat2_noncommute
#check @vec2Inner
#check @ropeApply
#check @ropeRotor_transpose
#check @planarInner_mulVec_right
#check @planarInner_mulVec_left
#check @rope_inner_product_relative_time_cancellation
#check @rope_inner_product_shift_invariant
#check @conformal_log_proper_time_interval
#check @cotangentSymplecticForm
#check @featureInner_zero_right
#check @featureInner_zero_left
#check @cotangentSymplecticForm_skew
#check @transactionalLogit_eq_scaled_cotangentSymplecticForm
#check @transactionalSoftmax_modularSurprisal_eq_cotangentAction

end InfoGeometry.Synthesis.TransactionalQueryKeyRoPEPhaseSpaceBridge.Audit
