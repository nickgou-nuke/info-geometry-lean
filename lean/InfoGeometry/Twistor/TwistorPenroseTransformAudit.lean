import InfoGeometry.Twistor.TwistorPenroseTransform

/-!
# Axiom Audit: Finite Twistor Spinor Arrays

Audits all theorems to ensure 0 debt, 0 custom axioms, and dependency strictly
on standard Lean 4 axioms: `[propext, Classical.choice, Quot.sound]`.
-/

open InfoGeometry.Twistor.TwistorPenroseTransform

#print axioms epsilon_antisymm
#print axioms contract_epsilon_symm
#print axioms TwistorMaxwellArrayData.symmetric_gradient_contraction_zero
#print axioms TwistorMaxwellArrayData.curvature_array_pair_antisymmetric
#print axioms TwistorMaxwellArrayData.curvature_array_epsilon_contraction_zero
#print axioms TwistorMaxwellArrayData.symmetric_array_contraction_readout
#print axioms incidence_homogeneous
#print axioms incidence_derivation_eq_zero
