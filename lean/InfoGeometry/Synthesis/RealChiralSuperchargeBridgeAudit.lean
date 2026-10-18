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

#check @superKKT_ladder_and_koszul_parastatistics_laws
#check @super_andreev_chiral_transmutation
#check @supercharge_nilpotent_on_lightcone
#check @koszul_brst_cohomology_souriau_massieu_invariance
#check @nativeCl55NullVectorAction_sq_zero
#check @nativeCl55WittAction_nilpotent_and_odd

#print axioms superKKT_ladder_and_koszul_parastatistics_laws
#print axioms super_andreev_chiral_transmutation
#print axioms supercharge_nilpotent_on_lightcone
#print axioms koszul_brst_cohomology_souriau_massieu_invariance
#print axioms nativeCl55NullVectorAction_sq_zero
#print axioms nativeCl55WittAction_nilpotent_and_odd

end InfoGeometry.Synthesis.RealChiralSuperchargeBridgeAudit
