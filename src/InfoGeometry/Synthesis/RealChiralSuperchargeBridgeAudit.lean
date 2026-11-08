/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Synthesis.RealChiralSuperchargeBridge

/-!
# Kernel audit for the finite matrix identities and native null-spinor facts

The first group audits the explicit finite matrix witnesses. The second group
audits the independent native `Cl(5,5)` null-vector action. No theorem here
identifies these constructions or asserts a super-KKT representation.
-/

namespace InfoGeometry.Synthesis.RealChiralSuperchargeBridgeAudit

open InfoGeometry.Synthesis.RealChiralSuperchargeBridge

#check @superKKTDual_koszulSign_and_vec3Cross_laws
#check @super_andreev_chiral_transmutation
#check @finiteMatrixWitnesses_squareZero_and_lightcone_norm_identity
#check @finiteMatrixTrace_and_souriauShift_invariance
#check @nativeCl55NullVectorAction_sq_zero
#check @nativeCl55WittAction_nilpotent_and_odd
#check @masterSuperchargeQ_odd_for_masterParity
#check @masterSuperchargeQBar_odd_for_masterParity
#check @masterSupercharge_anticommutator_even_for_masterParity

#print axioms superKKTDual_koszulSign_and_vec3Cross_laws
#print axioms super_andreev_chiral_transmutation
#print axioms finiteMatrixWitnesses_squareZero_and_lightcone_norm_identity
#print axioms finiteMatrixTrace_and_souriauShift_invariance
#print axioms nativeCl55NullVectorAction_sq_zero
#print axioms nativeCl55WittAction_nilpotent_and_odd
#print axioms masterSuperchargeQ_odd_for_masterParity
#print axioms masterSuperchargeQBar_odd_for_masterParity
#print axioms masterSupercharge_anticommutator_even_for_masterParity

end InfoGeometry.Synthesis.RealChiralSuperchargeBridgeAudit
