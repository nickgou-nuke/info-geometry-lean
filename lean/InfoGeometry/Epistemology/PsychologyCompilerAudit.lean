import InfoGeometry.Epistemology.PsychologyCompiler

/-!
# Audit Module: PsychologyCompilerAudit

Audits and confirms axiom counts for `InfoGeometry.Epistemology.PsychologyCompiler`.
Strictly verifies that all theorems depend only on standard Lean foundational axioms
`[propext, Classical.choice, Quot.sound]` with 0 sorry and 0 admit.
-/

namespace InfoGeometry.Epistemology.PsychologyCompilerAudit

open InfoGeometry.Epistemology.PsychologyCompiler

#print axioms EpistemicStage.rank_injective
#print axioms EpistemicStage.prima_materia_is_bottom
#print axioms EpistemicStage.chiral_syzygy_le_individuation
#print axioms QuadraticResponse.response_at_optimal
#print axioms QuadraticResponse.activity_is_gauge_invariant
#print axioms QuadraticResponse.response_is_gauge_invariant
#print axioms syzygy_balance
#print axioms distillation_is_monotone
#print axioms compile_psychology_compiler

end InfoGeometry.Epistemology.PsychologyCompilerAudit
