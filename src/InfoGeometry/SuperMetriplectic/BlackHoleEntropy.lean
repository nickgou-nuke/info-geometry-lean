import InfoGeometry.SuperMetriplectic.BPS
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# BPS Black-Hole Entropy Packets

Conservative body-level interface for the final BPS black-hole entropy picture.

This file intentionally does not assert a global `Cl(4,4) ≃ M₁₆(ℝ)` theorem,
nor does it construct split-octonionic Zorn matrices.  It records the pieces
that can be connected to such models later:

* a quartic charge invariant as a Casimir readout;
* a horizon-entropy readout;
* a microscopic Witten-index logarithmic readout;
* BPS/Onsager protection inherited from `BPSSuperMetriplecticCapstone`.
-/

namespace InfoGeometry.SuperMetriplectic

/--
Scalar shadow of a `Cl(4,4)`/TKK charge orbit.

The electric and magnetic entries are placeholders for the eventual charge
vector components.  The quartic invariant is kept as a supplied scalar readout;
the file does not construct it from a concrete Jordan triple or Zorn matrix.
-/
structure Cl44BPSChargeOrbitPacket where
  electricChargeReadout : ℝ
  magneticChargeReadout : ℝ
  quarticInvariant : ℝ
  casimirReadout : ℝ
  horizonEntropy : ℝ
  wittenLogReadout : ℝ
  casimir_eq_quarticInvariant :
    casimirReadout = quarticInvariant
  horizonEntropy_eq_casimirEntropy :
    horizonEntropy = casimirReadout
  wittenLogReadout_eq_horizonEntropy :
    wittenLogReadout = horizonEntropy

namespace Cl44BPSChargeOrbitPacket

/-- The quartic invariant is represented as the coadjoint-orbit Casimir readout. -/
theorem casimir_eq_quartic (P : Cl44BPSChargeOrbitPacket) :
    P.casimirReadout = P.quarticInvariant :=
  P.casimir_eq_quarticInvariant

/-- Horizon entropy is the Casimir entropy readout in this packet. -/
theorem horizonEntropy_eq_casimir
    (P : Cl44BPSChargeOrbitPacket) :
    P.horizonEntropy = P.casimirReadout :=
  P.horizonEntropy_eq_casimirEntropy

/-- The microscopic Witten-index log readout matches the horizon entropy. -/
theorem wittenLog_eq_horizonEntropy
    (P : Cl44BPSChargeOrbitPacket) :
    P.wittenLogReadout = P.horizonEntropy :=
  P.wittenLogReadout_eq_horizonEntropy

/-- Horizon entropy can be read through the quartic invariant/Casimir lane. -/
theorem horizonEntropy_eq_quarticInvariant
    (P : Cl44BPSChargeOrbitPacket) :
    P.horizonEntropy = P.quarticInvariant := by
  rw [P.horizonEntropy_eq_casimir, P.casimir_eq_quartic]

/-- Microscopic and macroscopic entropy readouts agree. -/
theorem wittenLogReadout_eq_quarticEntropy
    (P : Cl44BPSChargeOrbitPacket) :
    P.wittenLogReadout = P.quarticInvariant := by
  rw [P.wittenLog_eq_horizonEntropy, P.horizonEntropy_eq_quarticInvariant]

end Cl44BPSChargeOrbitPacket

/--
Zorn-style even/odd entropy split at scalar-body level.

This is not a concrete split-octonion multiplication table.  It only records
the expected bookkeeping: even/bosonic and odd/fermionic entropy channels
combine to the same total body entropy readout.
-/
structure ZornEvenOddEntropySplit where
  evenBosonicReadout : ℝ
  oddFermionicReadout : ℝ
  cancellationReadout : ℝ
  totalBodyEntropy : ℝ
  total_eq_even_plus_odd_minus_cancellation :
    totalBodyEntropy =
      evenBosonicReadout + oddFermionicReadout - cancellationReadout

namespace ZornEvenOddEntropySplit

/-- Public scalar-body even/odd entropy bookkeeping equation. -/
theorem total_eq
    (Z : ZornEvenOddEntropySplit) :
    Z.totalBodyEntropy =
      Z.evenBosonicReadout + Z.oddFermionicReadout - Z.cancellationReadout :=
  Z.total_eq_even_plus_odd_minus_cancellation

end ZornEvenOddEntropySplit

/--
Black-hole BPS entropy capstone.

It joins the BPS/Witten thermodynamic capstone with the `Cl(4,4)` charge-orbit
entropy readout and an optional even/odd Zorn-style entropy split.
-/
structure BPSBlackHoleEntropyCapstone
    (V : Type*) [AddCommGroup V] [Module ℝ V] where
  superCapstone : BPSSuperMetriplecticCapstone V
  chargeOrbit : Cl44BPSChargeOrbitPacket
  zornSplit : ZornEvenOddEntropySplit
  zorn_total_matches_horizon :
    zornSplit.totalBodyEntropy = chargeOrbit.horizonEntropy

namespace BPSBlackHoleEntropyCapstone

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The protected BPS dissipative readout vanishes. -/
theorem protected_flow_readout_zero
    (C : BPSBlackHoleEntropyCapstone V) :
    C.superCapstone.protectedFlowReadout = 0 :=
  C.superCapstone.protected_flow_readout_zero

/-- The Witten-index temperature derivative vanishes. -/
theorem witten_temperature_derivative_zero
    (C : BPSBlackHoleEntropyCapstone V) :
    C.superCapstone.witten.temperatureDerivative = 0 :=
  C.superCapstone.witten_temperature_derivative_zero

/-- The microscopic Witten-index log readout matches the horizon entropy. -/
theorem microscopic_entropy_eq_horizonEntropy
    (C : BPSBlackHoleEntropyCapstone V) :
    C.chargeOrbit.wittenLogReadout = C.chargeOrbit.horizonEntropy :=
  C.chargeOrbit.wittenLog_eq_horizonEntropy

/-- The horizon entropy is the quartic-invariant/Casimir readout. -/
theorem horizonEntropy_eq_quarticInvariant
    (C : BPSBlackHoleEntropyCapstone V) :
    C.chargeOrbit.horizonEntropy = C.chargeOrbit.quarticInvariant :=
  C.chargeOrbit.horizonEntropy_eq_quarticInvariant

/-- The even/odd Zorn-style total agrees with the horizon entropy. -/
theorem zorn_totalBodyEntropy_eq_horizonEntropy
    (C : BPSBlackHoleEntropyCapstone V) :
    C.zornSplit.totalBodyEntropy = C.chargeOrbit.horizonEntropy :=
  C.zorn_total_matches_horizon

/-- Entropy production remains nonnegative in the underlying metriplectic flow. -/
theorem entropyProduction_nonnegative
    (C : BPSBlackHoleEntropyCapstone V) :
    0 ≤ C.superCapstone.flow.entropyProduction :=
  C.superCapstone.entropyProduction_nonnegative

/--
Combined black-hole entropy capstone:
BPS protection, Witten-index invariance, microscopic/macroscopic entropy
matching, quartic-Casimir readout, Zorn split matching, and the second law.
-/
theorem bps_blackHole_entropy_capstone
    (C : BPSBlackHoleEntropyCapstone V) :
    C.superCapstone.protectedFlowReadout = 0
      ∧ C.superCapstone.witten.temperatureDerivative = 0
      ∧ C.chargeOrbit.wittenLogReadout = C.chargeOrbit.horizonEntropy
      ∧ C.chargeOrbit.horizonEntropy = C.chargeOrbit.quarticInvariant
      ∧ C.zornSplit.totalBodyEntropy = C.chargeOrbit.horizonEntropy
      ∧ 0 ≤ C.superCapstone.flow.entropyProduction := by
  exact ⟨C.protected_flow_readout_zero,
    C.witten_temperature_derivative_zero,
    C.microscopic_entropy_eq_horizonEntropy,
    C.horizonEntropy_eq_quarticInvariant,
    C.zorn_totalBodyEntropy_eq_horizonEntropy,
    C.entropyProduction_nonnegative⟩

end BPSBlackHoleEntropyCapstone

end InfoGeometry.SuperMetriplectic
