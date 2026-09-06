/-
InfoGeometry/OperatorAlgebra/KapustinWittenDuality.lean

Operator-level Kapustin-Witten / S-duality interface.

This module does not prove geometric Langlands.

It formalizes the safe operator skeleton:

  Wilson electric readout
    ↔ 't Hooft magnetic readout

under a supplied S-duality map.

The theorem payload is transport of an eigen/readout condition across a
duality property. The geometric Langlands interpretation is kept as a separate
property-gated interface.
-/

import Mathlib.Tactic

noncomputable section

namespace InfoGeometry.OperatorAlgebra.KapustinWittenDuality

/-! ## 1. Electric and magnetic operator ledgers -/

/--
An electric/Wilson operator ledger.

`State` is the carrier of physical/operator states.
`Charge` is the scalar, character, or readout type.
-/
structure WilsonLedger
    (State Charge : Type*) where
  /-- Wilson/electric operator action. -/
  Wilson : State → State

  /-- Electric character/readout. -/
  electricReadout : State → Charge

/-- A magnetic/'t Hooft operator ledger. -/
structure THooftLedger
    (State Charge : Type*) where
  /-- 't Hooft/magnetic operator action. -/
  THooft : State → State

  /-- Magnetic character/readout. -/
  magneticReadout : State → Charge

/-! ## 2. Eigen/readout predicates -/

/--
A Wilson eigenstate/eigenreadout condition.

This is deliberately abstract over the charge object. In concrete models,
`Charge` may be `ℂ`, a character group, a representation label, or a
topological charge.
-/
def IsWilsonEigen
    {State Charge : Type*}
    (W : WilsonLedger State Charge)
    (ψ : State)
    (χ : Charge) : Prop :=
  W.electricReadout (W.Wilson ψ) = χ

/-- A 't Hooft eigenstate/eigenreadout condition. -/
def IsTHooftEigen
    {State Charge : Type*}
    (T : THooftLedger State Charge)
    (ψ : State)
    (χ : Charge) : Prop :=
  T.magneticReadout (T.THooft ψ) = χ

/-! ## 3. S-duality exchange datum -/

/--
Operator S-duality datum.

This is the finite proof-carrying replacement for the slogan:

  Wilson operators on one side correspond to 't Hooft operators on the dual
  side.

The map `dualize` transports states from the electric theory to the magnetic
dual theory.

The law `wilson_to_thooft_readout` says the Wilson readout of a state equals
the 't Hooft readout of its S-dual state.
-/
structure SDualityDatum
    (ElectricState MagneticState Charge : Type*) where
  electric :
    WilsonLedger ElectricState Charge

  magnetic :
    THooftLedger MagneticState Charge

  /-- S-duality transport of states. -/
  dualize :
    ElectricState → MagneticState

  /-- Electric Wilson readout equals magnetic 't Hooft readout after duality. -/
  wilson_to_thooft_readout :
    ∀ ψ : ElectricState,
      electric.electricReadout (electric.Wilson ψ) =
        magnetic.magneticReadout (magnetic.THooft (dualize ψ))

namespace SDualityDatum

variable
    {ElectricState MagneticState Charge : Type*}

variable
    (S : SDualityDatum ElectricState MagneticState Charge)

/-- S-duality transports Wilson eigenconditions to 't Hooft eigenconditions. -/
theorem wilsonEigen_transports_to_tHooftEigen
    {ψ : ElectricState}
    {χ : Charge}
    (hψ : IsWilsonEigen S.electric ψ χ) :
    IsTHooftEigen S.magnetic (S.dualize ψ) χ := by
  unfold IsWilsonEigen at hψ
  unfold IsTHooftEigen
  rw [← S.wilson_to_thooft_readout ψ]
  exact hψ

/-- Equivalent readout form of Wilson/'t Hooft duality. -/
theorem tHooft_readout_eq_wilson_readout
    (ψ : ElectricState) :
    S.magnetic.magneticReadout
        (S.magnetic.THooft (S.dualize ψ))
      =
    S.electric.electricReadout
        (S.electric.Wilson ψ) := by
  exact (S.wilson_to_thooft_readout ψ).symm

end SDualityDatum

/-! ## 4. Pairing-preserving duality -/

/--
A duality datum with an explicit pairing.

This is useful for index, charge, or K-homology pairings.
-/
structure PairingDualityDatum
    (ElectricState MagneticState Charge PairingValue : Type*) where
  sDuality :
    SDualityDatum ElectricState MagneticState Charge

  /-- Electric pairing/readout. -/
  electricPairing :
    ElectricState → Charge → PairingValue

  /-- Magnetic pairing/readout. -/
  magneticPairing :
    MagneticState → Charge → PairingValue

  /-- Pairing preservation under duality. -/
  pairing_preserved :
    ∀ (ψ : ElectricState) (χ : Charge),
      electricPairing ψ χ =
        magneticPairing (sDuality.dualize ψ) χ

namespace PairingDualityDatum

variable
    {ElectricState MagneticState Charge PairingValue : Type*}

variable
    (P : PairingDualityDatum
      ElectricState MagneticState Charge PairingValue)

/-- Electric and magnetic pairings agree after S-duality. -/
theorem electricPairing_eq_magneticPairing
    (ψ : ElectricState)
    (χ : Charge) :
    P.electricPairing ψ χ =
      P.magneticPairing (P.sDuality.dualize ψ) χ :=
  P.pairing_preserved ψ χ

end PairingDualityDatum

/-- S-duality transports Wilson eigenconditions to 't Hooft eigenconditions. -/
theorem operator_s_duality :
    ∀ (ElectricState MagneticState Charge : Type*),
      ∀ S : SDualityDatum ElectricState MagneticState Charge,
        ∀ (ψ : ElectricState) (χ : Charge),
          IsWilsonEigen S.electric ψ χ →
            IsTHooftEigen S.magnetic (S.dualize ψ) χ := by
  intro ElectricState MagneticState Charge S ψ χ hψ
  exact S.wilsonEigen_transports_to_tHooftEigen hψ

theorem wilsonEigen_transports_to_tHooftEigen_direct
    {ElectricState MagneticState Charge : Type*}
    (electric : WilsonLedger ElectricState Charge)
    (magnetic : THooftLedger MagneticState Charge)
    (dualize : ElectricState → MagneticState)
    (readout_eq : ∀ ψ : ElectricState,
      electric.electricReadout (electric.Wilson ψ) =
        magnetic.magneticReadout (magnetic.THooft (dualize ψ)))
    {ψ : ElectricState} {χ : Charge}
    (hψ : IsWilsonEigen electric ψ χ) :
    IsTHooftEigen magnetic (dualize ψ) χ := by
  unfold IsWilsonEigen at hψ
  unfold IsTHooftEigen
  rw [← readout_eq ψ]
  exact hψ

theorem pairing_preserved_direct
    {ElectricState MagneticState Charge PairingValue : Type*}
    (electricPairing : ElectricState → Charge → PairingValue)
    (magneticPairing : MagneticState → Charge → PairingValue)
    (dualize : ElectricState → MagneticState)
    (pairing_eq : ∀ (ψ : ElectricState) (χ : Charge),
      electricPairing ψ χ = magneticPairing (dualize ψ) χ)
    (ψ : ElectricState) (χ : Charge) :
    electricPairing ψ χ = magneticPairing (dualize ψ) χ :=
  pairing_eq ψ χ

end InfoGeometry.OperatorAlgebra.KapustinWittenDuality
