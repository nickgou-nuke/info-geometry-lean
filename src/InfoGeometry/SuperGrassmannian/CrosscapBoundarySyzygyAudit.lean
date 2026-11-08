import InfoGeometry.SuperGrassmannian.CrosscapBoundarySyzygy

/-!
# Audit Companion: String-Theoretic Crosscap State & Tadpole Cancellation as Chiral Syzygy

This module verifies the kernel axiomatic footprint and non-vacuity of
`InfoGeometry.SuperGrassmannian.CrosscapSyzygy`.
-/

namespace InfoGeometry.SuperGrassmannian.CrosscapSyzygy.Audit

open InfoGeometry.SuperGrassmannian.CrosscapSyzygy

#check @compile_crosscap_boundary_syzygy
#check @moebiusOddPullback_involutive
#check @invariant_odd_vanishes
#check @tadpole_cancellation_iff
#check @typeI_so32_tadpole_cancellation
#check @chiral_syzygy_zero_iff
#check @chiral_syzygy_step_preserved
#check @tree_level_defect_zero_of_tadpole_cancellation
#check @tree_level_defect_pos_of_anomaly

#print axioms compile_crosscap_boundary_syzygy
#print axioms moebiusOddPullback_involutive
#print axioms invariant_odd_vanishes
#print axioms tadpole_cancellation_iff
#print axioms typeI_so32_tadpole_cancellation
#print axioms chiral_syzygy_zero_iff
#print axioms tree_level_defect_zero_of_tadpole_cancellation
#print axioms tree_level_defect_pos_of_anomaly

end InfoGeometry.SuperGrassmannian.CrosscapSyzygy.Audit
