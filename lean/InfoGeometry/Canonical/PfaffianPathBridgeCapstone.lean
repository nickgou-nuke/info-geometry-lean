import InfoGeometry.Volume.PfaffianPathBridge

namespace InfoGeometry.Canonical.PfaffianPathBridgeCapstone

open InfoGeometry.Volume.PfaffianPathBridge

theorem pfaffian_path_bridge_capstone
    (P : PfaffianPathBridgePacket) :
    P.pfaffianPairings.pfaffianAmplitude ^ 2 =
        P.pfaffianPairings.determinantEvenVolume ∧
      P.pfaffianPairings.pfaffianAmplitude =
        P.pfaffianPairings.matchingExpansion ∧
      P.pfaffianPairings.determinantEvenVolume =
        P.pfaffianPairings.pfaffianAmplitude ^ 2 := by
  exact ⟨constructPfaffianPathBridgeTarget P,
    pfaffian_eq_fermionic_pairing P,
    determinant_even_volume_eq_pfaffian_sq_bridge P⟩

end InfoGeometry.Canonical.PfaffianPathBridgeCapstone
