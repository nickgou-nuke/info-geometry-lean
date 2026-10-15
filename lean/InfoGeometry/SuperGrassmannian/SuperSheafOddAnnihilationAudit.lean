import InfoGeometry.SuperGrassmannian.SuperSheafOddAnnihilation

/-!
# Audit Companion: Epistemic Sheaf Invariance & Odd Anomaly Annihilation

This module verifies the kernel axiomatic footprint and non-vacuity of
`InfoGeometry.SuperGrassmannian.SheafAnnihilation`.
-/

namespace InfoGeometry.SuperGrassmannian.SheafAnnihilation.Audit

open InfoGeometry.SuperGrassmannian.SheafAnnihilation

#check @compile_super_sheaf_odd_annihilation
#check @moebiusPullback_involutive
#check @odd_anomaly_annihilated_at_crosscap
#check @even_body_invariant_at_crosscap
#check @paired_even2_invariant_at_crosscap
#check @isolated_odd_anomaly_rejected
#check @balanced_syzygy_is_sheaf_section

#print axioms compile_super_sheaf_odd_annihilation
#print axioms moebiusPullback_involutive
#print axioms odd_anomaly_annihilated_at_crosscap
#print axioms even_body_invariant_at_crosscap
#print axioms isolated_odd_anomaly_rejected
#print axioms balanced_syzygy_is_sheaf_section

end InfoGeometry.SuperGrassmannian.SheafAnnihilation.Audit
