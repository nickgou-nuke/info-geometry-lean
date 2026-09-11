import InfoGeometry.Twistor.TwistorPenroseTransform

/-!
# Axiom Audit: TwistorPenroseTransform

Audits all theorems to ensure 0 debt, 0 custom axioms, and dependency strictly
on standard Lean 4 axioms: `[propext, Classical.choice, Quot.sound]`.
-/

open InfoGeometry.Twistor.TwistorPenroseTransform

#print axioms epsilon_antisymm
#print axioms contract_epsilon_symm
#print axioms TwistorMaxwellCohomology.zero_rest_mass_equation
#print axioms TwistorMaxwellCohomology.maxwell_antisymmetry
#print axioms TwistorMaxwellCohomology.maxwell_anti_self_dual_part_vanishes
#print axioms TwistorMaxwellCohomology.maxwell_source_free_divergence
#print axioms incidence_homogeneous
#print axioms certified_twistor_penrose_transform_synthesis
