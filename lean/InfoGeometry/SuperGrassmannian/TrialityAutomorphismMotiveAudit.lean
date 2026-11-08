import InfoGeometry.SuperGrassmannian.TrialityAutomorphismMotive

/-!
# Audit File: TrialityAutomorphismMotiveAudit

This file verifies that `compile_triality_automorphism_motive` compiles cleanly
and depends only on standard Lean foundational axioms: `[propext, Classical.choice, Quot.sound]`.
-/

namespace InfoGeometry.SuperGrassmannian.TrialityAutomorphismMotive.Audit

open InfoGeometry.SuperGrassmannian.TrialityAutomorphismMotive

#check compile_triality_automorphism_motive
#print axioms compile_triality_automorphism_motive

end InfoGeometry.SuperGrassmannian.TrialityAutomorphismMotive.Audit
