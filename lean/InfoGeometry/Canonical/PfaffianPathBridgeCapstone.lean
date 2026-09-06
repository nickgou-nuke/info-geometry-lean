import InfoGeometry.Volume.PfaffianPathBridge

namespace InfoGeometry.Canonical.PfaffianPathBridgeCapstone

open InfoGeometry.Volume.PfaffianPathBridge

theorem pfaffian_path_bridge_canonical_capstone :
    (PfaffianMatchingExpansionPacket.ofEmpty.pfaffianAmplitude ^ 2 =
      PfaffianMatchingExpansionPacket.ofEmpty.determinantEvenVolume) ∧
    (∀ a : ℝ,
      (PfaffianMatchingExpansionPacket.ofTwoByTwo a).pfaffianAmplitude ^ 2 =
        (PfaffianMatchingExpansionPacket.ofTwoByTwo a).determinantEvenVolume ∧
      (PfaffianMatchingExpansionPacket.ofTwoByTwo a).pfaffianAmplitude = a) := by
  constructor
  · exact PfaffianMatchingExpansionPacket.ofEmpty.pfaffian_sq_eq_determinantEvenVolume
  · intro a
    exact ⟨PfaffianMatchingExpansionPacket.ofTwoByTwo a
      |>.pfaffian_sq_eq_determinantEvenVolume, rfl⟩

end InfoGeometry.Canonical.PfaffianPathBridgeCapstone
