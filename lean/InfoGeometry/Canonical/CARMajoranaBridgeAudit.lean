/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.CARMajoranaOwnerAdapters
import InfoGeometry.Canonical.MajoranaPfaffianKernelAudit

/-! Kernel axiom footprints for the explicit CAR-to-chain bridge. -/
open InfoGeometry.Canonical

#print axioms CARMajoranaFiniteBridge.majorana1_from_car
#print axioms CARMajoranaFiniteBridge.majorana2_from_car
#print axioms CARMajoranaFiniteBridge.twoSiteMajorana_car
#print axioms CARMajoranaFiniteBridge.twoSiteMajorana_selfAdjoint
#print axioms CARMajoranaFiniteBridge.twoSiteMajorana_ne_zero
#print axioms CARMajoranaFiniteBridge.fourMode_pfaffian_iff_conserved_field
#print axioms CARMajoranaFiniteBridge.sweetSpot_chain_commutator_eq_zero_iff
#print axioms CARMajoranaFiniteBridge.sweetSpot_pfaffian_iff_conserved_chain
#print axioms CARMajoranaFiniteBridge.car_to_chain_to_pfaffian
#print axioms CARMajoranaOwnerAdapters.creation_coordinates
#print axioms CARMajoranaOwnerAdapters.annihilation_coordinates
#print axioms CARMajoranaOwnerAdapters.sweetSpot_boundary_commutes
