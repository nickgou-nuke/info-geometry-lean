/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.AttentionGNSRatioWeightedBridge

/-!
# Axiom audit for the attention/GNS ratio-weighted Markov bridge
-/

namespace InfoGeometry.QuantumContext.AttentionGNSRatioWeightedBridge.Audit

open InfoGeometry.QuantumContext.AttentionGNSRatioWeightedBridge

#print axioms ratioToGns_gnsToRatio
#print axioms gnsToRatio_ratioToGns
#print axioms ratioWeightedPairing_eq_gnsAfterTransport
#print axioms transportedMarkovCompression_gns_selfAdjoint
#print axioms attentionTransportedMarkovCompression_gns_selfAdjoint
#print axioms attentionSelectedColimit_transportedCompression_selfAdjoint

end InfoGeometry.QuantumContext.AttentionGNSRatioWeightedBridge.Audit
