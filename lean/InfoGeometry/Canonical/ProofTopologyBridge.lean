import InfoGeometry.Causal.Sensing

/-!
# InfoGeometry.Canonical.ProofTopologyBridge

Canonical bridge for the finite proof-topology layer.
-/

namespace InfoGeometry.Canonical.ProofTopologyBridge

open InfoGeometry.Causal.Sensing
open InfoGeometry.Causal.ProofTopology

variable {World Proof : Type*} [Preorder World] [Preorder Proof]

theorem sensor_maps_forward
    (S : Sensor World Proof) {a b : World}
    (h : b ∈ forwardCone a) : S.sense b ∈ forwardCone (S.sense a) :=
  S.monotone_sense h

theorem sensor_maps_backward
    (S : Sensor World Proof) {a b : World}
    (h : b ∈ backwardCone a) : S.sense b ∈ backwardCone (S.sense a) :=
  S.monotone_sense h

theorem faithful_sensor_reflects_order
    (S : FaithfulSensor World Proof) {a b : World} (h : S.sense a ≤ S.sense b) :
    a ≤ b :=
  S.reflects_order h

theorem faithful_sensor_reflects_no_loop
    (S : FaithfulSensor World Proof) {a b : World}
    (hab : S.sense a ≤ S.sense b) (hba : S.sense b ≤ S.sense a) :
    a ≤ b ∧ b ≤ a :=
  ⟨S.reflects_order hab, S.reflects_order hba⟩

end InfoGeometry.Canonical.ProofTopologyBridge
