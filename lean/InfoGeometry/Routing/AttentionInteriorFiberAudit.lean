/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Routing.AttentionInteriorFiber

/-!
# Kernel axiom audit for attention readout non-identifiability

These declarations concern finite probability rows and their value readout.
They do not identify an additive attention mask with a Peirce decomposition.
-/

#print axioms InfoGeometry.Routing.AttentionInteriorFiber.collinear_counterexample
#print axioms InfoGeometry.Routing.AttentionInteriorFiber.collinear_softmax_realization
#print axioms InfoGeometry.Routing.AttentionInteriorFiber.exists_distinct_positive_same_readout
#print axioms InfoGeometry.Routing.AttentionInteriorFiber.unique_probability_coords_at_positive_iff
#print axioms InfoGeometry.Routing.AttentionInteriorFiber.softmax_nonidentifiable
