/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Cosmology.GNSQuotientCosetEquivalence

/-!
# Audit for GNSQuotientCosetEquivalence

This audit file prints the axioms of all key theorems and constructions in
`InfoGeometry.Cosmology.GNSQuotientCosetEquivalence` to certify that they depend
exclusively on standard Lean 4 / Mathlib axioms:
`[propext, Classical.choice, Quot.sound]`.
-/

namespace InfoGeometry.Cosmology.GNSQuotientCoset.Audit

-- Section 1: GNS Vacuum and Quotient Module
#print axioms cyclicVacuum_ne_zero
#print axioms mem_gnsRadicalSubmodule_iff
#print axioms evalVacuum_surjective
#print axioms gnsQuotientEquiv
#print axioms gnsQuotientEquiv_mk
#print axioms gns_quotient_left_action_intertwining

-- Section 2: Orbit-Stabilizer Coset Equivalence
#print axioms rayEquiv_refl
#print axioms rayEquiv_symm
#print axioms rayEquiv_trans
#print axioms sl2Inv_mul
#print axioms mul_sl2Inv
#print axioms mulVec_ne_zero_of_isSL2
#print axioms rayEquiv_vacuum_iff_parabolic

-- Section 3: Projective GNS State Space Equivalence
#print axioms rayEquivGNS_refl
#print axioms rayEquivGNS_symm
#print axioms rayEquivGNS_trans
#print axioms rayEquiv_iff_rayEquivGNS
#print axioms projectiveGNSEquivProjectiveLine

-- Section 4: Krein Bogoliubov Flow and CAR Intertwining
#print axioms rootPlus_sq
#print axioms rootMinus_sq
#print axioms anticomm_rootPlus_rootMinus
#print axioms conjSL2_anticomm
#print axioms conjSL2_one
#print axioms isSL2_bogoliubovMatrix
#print axioms bogoliubov_krein_isometry
#print axioms bogoliubov_preserves_car

end InfoGeometry.Cosmology.GNSQuotientCoset.Audit
