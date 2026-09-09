import InfoGeometry.Canonical.PenroseSpinNetworkTwistorBridge

namespace InfoGeometry.Canonical.PenroseSpinNetworkTwistorCapstone

open InfoGeometry.Canonical.PenroseSpinNetwork

/-- The theorem-only public capstone for the existing Penrose/twistor bridge. -/
theorem penrose_spin_network_canonical_capstone
    (c : TwistorLightConeCoordinates)
    (H : ChiralHelicityDatum)
    (h_bal : H.nLeft = H.nRight) :
    (spinHalfReadout true - spinHalfReadout false = 1) ∧
    ((leftTwistor c - rightTwistor c) / 2 = c.xi) ∧
    ((leftTwistor c + rightTwistor c) / 2 = c.tau) ∧
    (H.coords.xi = 0) ∧
    (leftTwistor H.coords = rightTwistor H.coords) := by
  refine ⟨spin_flip_step, rapidity_from_twistors c, time_from_twistors c,
    helicity_balance_rapidity_collapse H h_bal, ?_⟩
  exact (twistors_coincide_at_zero_helicity H h_bal).1

end InfoGeometry.Canonical.PenroseSpinNetworkTwistorCapstone
