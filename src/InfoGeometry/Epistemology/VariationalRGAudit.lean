import InfoGeometry.Epistemology.VariationalRG

/-!
# Audit Module: VariationalRGAudit

Audits and confirms axiom counts for `InfoGeometry.Epistemology.VariationalRG`.
Strictly verifies that all theorems depend only on standard Lean foundational axioms
`[propext, Classical.choice, Quot.sound]` with 0 sorry and 0 admit.
-/

namespace InfoGeometry.Epistemology.VariationalRGAudit

open InfoGeometry.Epistemology.VariationalRG

#print axioms pushforward
#print axioms markov_tv_contraction
#print axioms sigmoid_pos
#print axioms sigmoid_nonneg
#print axioms sigmoid_le_one
#print axioms one_sub_sigmoid_nonneg
#print axioms sigmoid_add_one_sub_sigmoid
#print axioms rbmBernoulliKernel
#print axioms compose
#print axioms pushforward_compose
#print axioms rg_layer_distinguishability_monotonicity
#print axioms fiber_observable_invariance
end InfoGeometry.Epistemology.VariationalRGAudit

