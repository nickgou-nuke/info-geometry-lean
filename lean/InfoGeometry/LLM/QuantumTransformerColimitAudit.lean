/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.LLM.QuantumTransformerColimitBridge

open InfoGeometry.LLM.Colimit

set_option linter.unusedVariables false

#print axioms attentionStageEmbedding_doubly_stochastic
#print axioms attentionStageTrace_preserving
#print axioms transformer_colimit_trace_comm
#print axioms canonicalTransformerTraceCocone
