/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.RelationalFieldStreamCausalPoset

/-!
# Axiomatic Audit: Relational Field Archetype Poset & Bistochastic Transport

This audit module inspects the axiom dependencies of the discrete archetype order,
Gibbs normalization, and bistochastic matrix closure theorems.
-/

namespace InfoGeometry.Canonical.RelationalFieldStream.Audit

#print axioms InfoGeometry.Canonical.RelationalFieldStream.causalPast_subset_iff
#print axioms InfoGeometry.Canonical.RelationalFieldStream.partition_pos
#print axioms InfoGeometry.Canonical.RelationalFieldStream.gibbsWeight_nonneg
#print axioms InfoGeometry.Canonical.RelationalFieldStream.gibbsWeight_sum_one
#print axioms InfoGeometry.Canonical.RelationalFieldStream.gibbsWeight_shift_invariant
#print axioms InfoGeometry.Canonical.RelationalFieldStream.one_is_bistochastic
#print axioms InfoGeometry.Canonical.RelationalFieldStream.convex_combination_bistochastic
#print axioms InfoGeometry.Canonical.RelationalFieldStream.decreasing_seq_bounded_by_initial
#print axioms InfoGeometry.Canonical.RelationalFieldStream.archetypeAdvance_eval
#print axioms InfoGeometry.Canonical.RelationalFieldStream.kernelVerification_causal_precedence

end InfoGeometry.Canonical.RelationalFieldStream.Audit
