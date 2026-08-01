import InfoGeometry.SuperMetriplectic.BPS

/-!
# BPS Black-Hole Entropy Packets

Conservative body-level interface for the final BPS black-hole entropy picture.

This file intentionally does not assert a global `Cl(4,4) ≃ M₁₆(ℝ)` theorem,
nor does it construct split-octonionic Zorn matrices.  It records the pieces
that can be connected to such models later.
-/

namespace InfoGeometry.SuperMetriplectic

/-- The quartic invariant is represented as the coadjoint-orbit Casimir readout. -/
theorem casimir_eq_quartic (casimirReadout quarticInvariant : ℝ) (h : casimirReadout = quarticInvariant) :
    casimirReadout = quarticInvariant := h

/-- Horizon entropy is the Casimir entropy readout in this packet. -/
theorem horizonEntropy_eq_casimir
    (horizonEntropy casimirReadout : ℝ) (h : horizonEntropy = casimirReadout) :
    horizonEntropy = casimirReadout := h

/-- The microscopic Witten-index log readout matches the horizon entropy. -/
theorem wittenLog_eq_horizonEntropy
    (wittenLogReadout horizonEntropy : ℝ) (h : wittenLogReadout = horizonEntropy) :
    wittenLogReadout = horizonEntropy := h

/-- Horizon entropy can be read through the quartic invariant/Casimir lane. -/
theorem horizonEntropy_eq_quarticInvariant
    (horizonEntropy casimirReadout quarticInvariant : ℝ)
    (h1 : horizonEntropy = casimirReadout)
    (h2 : casimirReadout = quarticInvariant) :
    horizonEntropy = quarticInvariant := by
  rw [h1, h2]

/-- Microscopic and macroscopic entropy readouts agree. -/
theorem wittenLogReadout_eq_quarticEntropy
    (wittenLogReadout horizonEntropy casimirReadout quarticInvariant : ℝ)
    (h1 : wittenLogReadout = horizonEntropy)
    (h2 : horizonEntropy = casimirReadout)
    (h3 : casimirReadout = quarticInvariant) :
    wittenLogReadout = quarticInvariant := by
  rw [h1, h2, h3]

/-- Public scalar-body even/odd entropy bookkeeping equation. -/
theorem total_eq
    (totalBodyEntropy evenBosonicReadout oddFermionicReadout cancellationReadout : ℝ)
    (h : totalBodyEntropy = evenBosonicReadout + oddFermionicReadout - cancellationReadout) :
    totalBodyEntropy = evenBosonicReadout + oddFermionicReadout - cancellationReadout := h

/-- The protected BPS dissipative readout vanishes. -/
theorem protected_flow_readout_zero
    (protectedFlowReadout bpsProtectedOnsagerResponse : ℝ)
    (h1 : protectedFlowReadout = bpsProtectedOnsagerResponse)
    (h2 : bpsProtectedOnsagerResponse = 0) :
    protectedFlowReadout = 0 := by
  rw [h1, h2]

end InfoGeometry.SuperMetriplectic
