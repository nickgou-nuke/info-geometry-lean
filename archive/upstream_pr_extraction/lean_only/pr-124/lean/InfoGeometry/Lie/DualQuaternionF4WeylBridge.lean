import InfoGeometry.Canonical.DualQuaternionF4WeylBridge

/-!
# Dual Quaternionic Realization of $W(F_4)$

This module forwards to the canonical owner implementation in
`InfoGeometry.Canonical.DualQuaternionF4WeylBridge`.
-/

namespace InfoGeometry.Lie.DualQuaternionF4WeylBridge

export InfoGeometry.Canonical.DualQuaternionF4WeylBridge (
  DualQuaternionF4WeylDatum
  dualQuaternionF4_e1_sq
  dualQuaternionF4_e2_sq
  dualQuaternionF4_e3_sq
  dualQuaternionF4_e4_sq
  dualQuaternionF4_e1e2_order3
  dualQuaternionF4_e2e3_order4
  dualQuaternionF4_e3e4_order3
  dualQuaternionF4_e1e3_commute
  dualQuaternionF4_e1e4_commute
  dualQuaternionF4_e2e4_commute
  dualQuaternionF4GeneratedSubgroup
  canonicalF4SimpleReflections
  dualQuaternionF4_eq_simpleReflections
  canonicalF4SimpleReflections_range
  dualQuaternionF4GeneratedSubgroup_eq_weylF4
)

end InfoGeometry.Lie.DualQuaternionF4WeylBridge
