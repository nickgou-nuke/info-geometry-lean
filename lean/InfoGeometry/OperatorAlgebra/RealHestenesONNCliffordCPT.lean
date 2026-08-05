import InfoGeometry.OperatorAlgebra.O44PinCPTReflectionBridge
import InfoGeometry.Canonical.BogoliubovTransport

/-!
# Real `O(4,4)` / `Pin(4,4)` Hestenes-CPT owner

This module keeps the concrete split-orthogonal and Pin data owned by
`O44PinCPTReflectionBridge`.  It does not introduce generic `Type*` witness
fields for Clifford, KAN, realness, or diagonal claims.  The diagonal datum,
when present, is an explicit Cartan shadow supplied by the concrete packet.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra

structure RealHestenesO44PinCPTPacket
    {V PinEl State Bog Kpart Apart Npart CartanShadow : Type*}
    [AddCommGroup V] [Module ℝ V]
    [Monoid PinEl] [Monoid Bog] where
  splitQuadratic44 : SplitQuadratic44 V
  fullO44Transform : Orthogonal44 splitQuadratic44
  pin44Cover : Pin44CoverDatum (V := V) (PinEl := PinEl) splitQuadratic44
  cptReflection :
    CPTPin44ReflectionCalibration splitQuadratic44 pin44Cover State
  realBogoliubovTransform : Bog
  kComponent : Kpart
  aComponent : Apart
  nComponent : Npart
  cartanDiagonalShadow : CartanShadow

end InfoGeometry.OperatorAlgebra
