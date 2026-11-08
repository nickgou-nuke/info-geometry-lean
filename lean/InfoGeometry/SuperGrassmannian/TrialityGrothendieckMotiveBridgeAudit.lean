import InfoGeometry.SuperGrassmannian.TrialityGrothendieckMotiveBridge

/-!
# Audit File: TrialityGrothendieckMotiveBridgeAudit

This file verifies that `compile_triality_grothendieck_motive` compiles cleanly
and depends only on standard Lean foundational axioms: `[propext, Classical.choice, Quot.sound]`.
-/

namespace InfoGeometry.SuperGrassmannian.TrialityGrothendieck.Audit

open InfoGeometry.SuperGrassmannian.TrialityGrothendieck

#check compile_triality_grothendieck_motive
#print axioms compile_triality_grothendieck_motive

end InfoGeometry.SuperGrassmannian.TrialityGrothendieck.Audit
