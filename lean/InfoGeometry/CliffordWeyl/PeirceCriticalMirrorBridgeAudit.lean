import InfoGeometry.CliffordWeyl.PeirceCriticalMirrorBridge

/-!
# Axiom audit: critical-mirror / Pauli coordinate transport

This file audits the actual cross-carrier results and the algebraic dilation
consequence. The underlying zeta projector laws remain owned by
`ZetaCoordinateSymmetry`; this audit deliberately adds no bundled wrapper theorem.
The analytic functional equation and any claim about zeta zeros are outside scope.
-/

namespace InfoGeometry.CliffordWeyl.PeirceCriticalMirrorBridge.Audit

open InfoGeometry.CliffordWeyl.PeirceCriticalMirrorBridge

#print axioms peirceDiagonalToCritical_criticalToPeirceDiagonal
#print axioms criticalTangent_transports_to_Pleft
#print axioms criticalNormal_transports_to_Pright
#print axioms criticalLine_fixed_by_functionalDual
#print axioms criticalLine_invariant_under_conjugation
#print axioms dilation_real_eigenvalue_forces_critical

end InfoGeometry.CliffordWeyl.PeirceCriticalMirrorBridge.Audit
