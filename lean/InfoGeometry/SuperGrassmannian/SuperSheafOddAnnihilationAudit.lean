/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.SuperGrassmannian.SuperSheafOddAnnihilation

/-!
# Audit Companion: Signed Pullback and Two-Torsion

This module checks the API and prints the kernel axiomatic footprint of
`InfoGeometry.SuperGrassmannian.SheafAnnihilation`.
-/

namespace InfoGeometry.SuperGrassmannian.SheafAnnihilation.Audit

open InfoGeometry.SuperGrassmannian.SheafAnnihilation

#check @odd_component_two_torsion_at_fixed
#check @identity_pullback_invariant_iff
#check @identity_pullback_invariant_of_two_eq_zero
#check @moebiusPullback_involutive
#check @odd_anomaly_annihilated_at_crosscap
#check @even_body_invariant_at_crosscap
#check @paired_even2_invariant_at_crosscap
#check @isolated_odd_anomaly_rejected
#check @balanced_syzygy_is_sheaf_section

#print axioms odd_component_two_torsion_at_fixed
#print axioms identity_pullback_invariant_iff
#print axioms identity_pullback_invariant_of_two_eq_zero
#print axioms moebiusPullback_involutive
#print axioms odd_anomaly_annihilated_at_crosscap
#print axioms even_body_invariant_at_crosscap
#print axioms isolated_odd_anomaly_rejected
#print axioms balanced_syzygy_is_sheaf_section

end InfoGeometry.SuperGrassmannian.SheafAnnihilation.Audit
