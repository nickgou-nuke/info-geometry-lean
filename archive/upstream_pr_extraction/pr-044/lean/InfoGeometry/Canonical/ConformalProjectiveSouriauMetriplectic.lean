import InfoGeometry.Canonical.Singular
import InfoGeometry.Topology.Metriplectic
import InfoGeometry.Projective.FiveGradedCentralizer

namespace InfoGeometry.Canonical.Unification

open InfoGeometry.Canonical
open InfoGeometry.Topology.Metriplectic
open InfoGeometry.Projective.Closure

/--
The unified Conformal Projective Souriau InfoGeometry.Topology.Metriplectic bridge.
This bundles the algebraic features of the Einstein anomaly,
metriplectic conservation, and Möbius index cancellation.
-/
structure ConformalProjectiveSouriauMetriplecticBridge (R : Type*) [CommRing R] [StarRing R] where
  /-- The underlying metriplectic structure -/
  metriplectic : MetriplecticStructure R
  
  /-- The underlying Möbius parity closure -/
  mobius : FiveGradedMobiusClosure 2
  
  /-- A base operator for the Einstein Anomaly -/
  a : R
  /-- Moore-Penrose inverse of `a` -/
  b_mp : R
  /-- Drazin inverse of `a` -/
  b_dr : R
  /-- Nilpotency index -/
  k : ℕ
  
  h_mp : IsMoorePenroseInverse a b_mp
  h_dr : IsDrazinInverse a b_dr k

namespace ConformalProjectiveSouriauMetriplecticBridge

variable {R : Type*} [CommRing R] [StarRing R]
variable (B : ConformalProjectiveSouriauMetriplecticBridge R)

/-- The Einstein anomaly associated with the bridge is skew-adjoint. -/
theorem anomaly_skew_adjoint
    (h_dr_star : star (B.a * B.b_dr) = B.a * B.b_dr) :
    star (EinsteinAnomaly B.a B.b_mp B.b_dr) = - (EinsteinAnomaly B.a B.b_mp B.b_dr) :=
  einsteinAnomaly_skew_adjoint B.a B.b_mp B.b_dr B.k B.h_mp B.h_dr h_dr_star

/-- InfoGeometry.Topology.Metriplectic energy is conserved. -/
theorem energy_conserved :
    totalEvolution B.metriplectic B.metriplectic.H = 0 :=
  energy_conservation B.metriplectic

/-- The Gromov-Witten index is resolved to zero when the Möbius parity is traceless. -/
theorem gw_index_resolved (h_traceless : Matrix.trace B.mobius.moebiusParity = 0) :
    B.mobius.gromovWittenIndex = 0 := by
  have h := zero_gromov_witten_anomaly_resolution 2 B.mobius h_traceless
  exact h.1

end ConformalProjectiveSouriauMetriplecticBridge

end InfoGeometry.Canonical.Unification
