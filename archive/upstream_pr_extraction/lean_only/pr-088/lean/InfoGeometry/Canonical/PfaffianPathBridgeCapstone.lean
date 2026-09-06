import InfoGeometry.Volume.PfaffianPathBridge

namespace InfoGeometry.Canonical.PfaffianPathBridgeCapstone

open InfoGeometry.Volume.PfaffianPathBridge

/-- Capstone 4: Verification of combinatorial Pfaffian expansion and 2x2 / vacuum determinant identity. -/
theorem pfaffian_path_bridge_canonical_capstone :
    -- 1. Empty/vacuum Pfaffian satisfies Pf² = det = 1
    (PfaffianMatchingExpansionPacket.ofEmpty.pfaffianAmplitude ^ 2 =
     PfaffianMatchingExpansionPacket.ofEmpty.determinantEvenVolume) ∧
    -- 2. 2x2 skew block satisfies Pf(W)² = det(W) = a²
    (∀ a : ℝ,
      (PfaffianMatchingExpansionPacket.ofTwoByTwo a).pfaffianAmplitude ^ 2 =
      (PfaffianMatchingExpansionPacket.ofTwoByTwo a).determinantEvenVolume ∧
      (PfaffianMatchingExpansionPacket.ofTwoByTwo a).pfaffianAmplitude = a) := by
  constructor
  · exact PfaffianMatchingExpansionPacket.ofEmpty.pfaffian_sq_eq_determinantEvenVolume
  · intro a
    constructor
    · exact (PfaffianMatchingExpansionPacket.ofTwoByTwo a).pfaffian_sq_eq_determinantEvenVolume
    · rfl

end InfoGeometry.Canonical.PfaffianPathBridgeCapstone
