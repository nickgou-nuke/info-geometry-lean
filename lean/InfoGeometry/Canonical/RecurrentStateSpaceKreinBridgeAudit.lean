import InfoGeometry.Canonical.RecurrentStateSpaceKreinBridge

/-!
# Audit Companion: Recurrent State Space & Krein Bridge

Independent audit file verifying that all declarations in
`InfoGeometry.Canonical.RecurrentStateSpaceKreinBridge` compile cleanly, have 0 `sorry`,
0 `admit`, and depend only on standard Lean 4 core foundational axioms:
`[propext, Classical.choice, Quot.sound]`.
-/

namespace InfoGeometry.Canonical.RecurrentStateSpaceKrein.Audit

#check @matMul2
#check @matId2
#check @kreinMetric
#check @bogoliubovMatrix
#check @kreinQuadForm
#check @mulVec
#check @bogoliubov_mul_add
#check @bogoliubov_zero
#check @kreinQuadForm_boost
#check @recurrentEvolution
#check @mulVec_matMul2
#check @mulVec_matId2
#check @recurrentEvolution_eq_accum
#check @recurrent_lightcone_preservation
#check @andreevReflection
#check @andreev_conjugates_bogoliubov

#print axioms bogoliubov_mul_add
#print axioms bogoliubov_zero
#print axioms kreinQuadForm_boost
#print axioms recurrentEvolution_eq_accum
#print axioms recurrent_lightcone_preservation
#print axioms andreev_conjugates_bogoliubov

end InfoGeometry.Canonical.RecurrentStateSpaceKrein.Audit
