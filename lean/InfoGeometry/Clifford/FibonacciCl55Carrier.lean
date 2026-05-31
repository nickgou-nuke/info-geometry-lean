import InfoGeometry.Clifford.ConformalLift55
import InfoGeometry.Canonical.FibonacciFiveGradeBridge

/-!
# InfoGeometry.Clifford.FibonacciCl55Carrier

A concrete `Cl(5,5)`-anchored carrier packet for the finite Fibonacci braid
bridge.

This file remains theorem-safe:

* it specializes the abstract five-grade Fibonacci bridge to the repo-owned
  split `Cl(5,5)` stage;
* it records an explicit conformal null pair in `Cl(5,5)`;
* it does **not** claim a concrete braid formula beyond the supplied witness;
* it packages the bridge as data, not as an unsupported identification.
-/

noncomputable section

namespace InfoGeometry.Clifford.FibonacciCl55Carrier

open InfoGeometry.Clifford.ConformalLift55
open InfoGeometry.Canonical.FibonacciFiveGradeBridge

/-- Repo-owned split `Cl(5,5)` stage. -/
abbrev Cl55 := ConformalLift55.Cl55

/--
Concrete `Cl(5,5)` carrier packet for the finite Fibonacci braid bridge.

The packet stores:

* a conformal null pair in `Cl(5,5)`;
* an explicit `Cl(5,5)`-valued Fibonacci bridge packet.
-/
structure CarrierPacket where
  /-- The conformal null pair living in the `Cl(5,5)` stage. -/
  nullPair : ConformalLift55.ConformalNullPair
  /-- The finite Fibonacci bridge instantiated on `Cl(5,5)`. -/
  bridge : FiveGradeFibonacciBridge Cl55

namespace CarrierPacket

/-- Read back the bridge packet as a first-class value. -/
def asBridge (C : CarrierPacket) : FiveGradeFibonacciBridge Cl55 := C.bridge

/-- The stored null pair is isotropic on the first leg. -/
theorem nullPair_u_square (C : CarrierPacket) : C.nullPair.u ^ 2 = 0 :=
  C.nullPair.u_square

/-- The stored null pair is isotropic on the second leg. -/
theorem nullPair_v_square (C : CarrierPacket) : C.nullPair.v ^ 2 = 0 :=
  C.nullPair.v_square

/-- The stored null pair anticommutes to the unit scalar. -/
theorem nullPair_anticomm (C : CarrierPacket) :
    C.nullPair.u * C.nullPair.v + C.nullPair.v * C.nullPair.u = 1 :=
  C.nullPair.anticomm

/-- The packet's Fibonacci matrix is involutive. -/
theorem fusionMatrix_sq (C : CarrierPacket) :
    C.asBridge.fusionMatrix * C.asBridge.fusionMatrix =
      (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  simpa [asBridge] using (C.bridge.fusionMatrix_sq)

/-- The packet's braid action preserves grade. -/
theorem braid_preserves_grade (C : CarrierPacket) (x : Cl55) :
    C.asBridge.inversion.grade (C.asBridge.braid x) =
      C.asBridge.inversion.grade x :=
  C.bridge.braid_preserves_grade x

/-- The packet's braid action preserves the computational sector. -/
theorem braid_preserves_computational (C : CarrierPacket) (x : Cl55)
    (hx : x ∈ C.asBridge.computationalSet) :
    C.asBridge.braid x ∈ C.asBridge.computationalSet :=
  C.bridge.braid_computational_preserving x hx

/-- The packet's braid action preserves the leakage sector. -/
theorem braid_preserves_leakage (C : CarrierPacket) (x : Cl55)
    (hx : x ∈ C.asBridge.leakageSet) :
    C.asBridge.braid x ∈ C.asBridge.leakageSet :=
  C.bridge.braid_leakage_preserving x hx

/-- The packet blocks leakage from the computational sector. -/
theorem braid_not_leakage_of_computational (C : CarrierPacket) (x : Cl55)
    (hx : x ∈ C.asBridge.computationalSet) :
    ¬ C.asBridge.braid x ∈ C.asBridge.leakageSet := by
  exact C.bridge.braid_not_leakage_of_computational hx

/-- The packet's braid action preserves the `+2` source sector. -/
theorem braid_preserves_source (C : CarrierPacket) (x : Cl55)
    (hx : x ∈ C.asBridge.inversion.sourceSet) :
    C.asBridge.braid x ∈ C.asBridge.inversion.sourceSet :=
  C.bridge.braid_preserves_source hx

/-- The packet's braid action preserves the `-2` sink sector. -/
theorem braid_preserves_sink (C : CarrierPacket) (x : Cl55)
    (hx : x ∈ C.asBridge.inversion.sinkSet) :
    C.asBridge.braid x ∈ C.asBridge.inversion.sinkSet :=
  C.bridge.braid_preserves_sink hx

/-- The packet's braid action preserves the outgoing boundary sector. -/
theorem braid_preserves_outgoing (C : CarrierPacket) (x : Cl55)
    (hx : x ∈ C.asBridge.inversion.outgoingSet) :
    C.asBridge.braid x ∈ C.asBridge.inversion.outgoingSet :=
  C.bridge.braid_preserves_outgoing hx

/-- The packet's braid action preserves the incoming boundary sector. -/
theorem braid_preserves_incoming (C : CarrierPacket) (x : Cl55)
    (hx : x ∈ C.asBridge.inversion.incomingSet) :
    C.asBridge.braid x ∈ C.asBridge.inversion.incomingSet :=
  C.bridge.braid_preserves_incoming hx

/-- The packet's braid action preserves the modular center. -/
theorem braid_preserves_center (C : CarrierPacket) (x : Cl55)
    (hx : x ∈ C.asBridge.inversion.centerSet) :
    C.asBridge.braid x ∈ C.asBridge.inversion.centerSet :=
  C.bridge.braid_preserves_center hx

end CarrierPacket

end InfoGeometry.Clifford.FibonacciCl55Carrier
