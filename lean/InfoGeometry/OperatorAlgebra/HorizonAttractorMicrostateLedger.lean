/-
InfoGeometry/OperatorAlgebra/HorizonAttractorMicrostateLedger.lean

Witness-gated black-hole / horizon microstate accounting ledger.

This module does not prove a black-hole entropy formula, attractor mechanism,
microstate counting theorem, or information recovery theorem.

It packages the operator-accounting shape already used elsewhere in the
project:

* charge/topological readout;
* central-charge readout;
* entropy/microstate readout;
* hidden memory reservoir;
* explicit attractor laws saying the selected readouts are determined by
  charge data;
* optional recovery witness saying hidden memory is visible under a supplied
  decoding channel.

Thermal/KMS readouts are kept separate from recovery: a thermal certificate by
itself does not decode hidden memory.
-/

import Mathlib
import InfoGeometry.Meta.OwnerTarget

noncomputable section

set_option linter.dupNamespace false

namespace InfoGeometry.OperatorAlgebra.HorizonAttractorMicrostateLedger

/-! ## 1. Horizon attractor accounting ledger -/

/--
Horizon attractor microstate ledger.

`State` is the horizon/operator state.
`Charge` is the conserved/topological charge datum.
`Scalar` is the codomain for entropy, central-charge, or index-like readouts.
`Memory` is the hidden microstate/grade-two/reservoir memory object.

The attractor laws are explicit equations: the horizon entropy and central
charge readouts are determined by the installed charge readout through supplied
functions.
-/
structure HorizonAttractorMicrostateLedger
    (State Charge Scalar Memory : Type*) where
  /-- Conserved/topological charge readout. -/
  chargeReadout :
    State → Charge

  /-- Central-charge or attractor-potential readout. -/
  centralCharge :
    State → Scalar

  /-- Entropy/microstate readout. -/
  entropyReadout :
    State → Scalar

  /-- Hidden memory/microstate reservoir. -/
  hiddenMemory :
    State → Memory

  /-- Entropy as a function of the installed charge datum. -/
  entropyOfCharge :
    Charge → Scalar

  /-- Central-charge readout as a function of the installed charge datum. -/
  centralChargeOfCharge :
    Charge → Scalar

  /-- Attractor-style entropy law. -/
  entropy_attractor_law :
    ∀ s : State,
      entropyReadout s = entropyOfCharge (chargeReadout s)

  /-- Attractor-style central-charge law. -/
  centralCharge_attractor_law :
    ∀ s : State,
      centralCharge s = centralChargeOfCharge (chargeReadout s)

namespace HorizonAttractorMicrostateLedger

variable
    {State Charge Scalar Memory : Type*}

variable
    (L : HorizonAttractorMicrostateLedger State Charge Scalar Memory)

/-- The horizon entropy readout is determined by charge data. -/
theorem entropyReadout_eq_entropyOfCharge
    (s : State) :
    L.entropyReadout s = L.entropyOfCharge (L.chargeReadout s) :=
  L.entropy_attractor_law s

/-- The central-charge readout is determined by charge data. -/
theorem centralCharge_eq_centralChargeOfCharge
    (s : State) :
    L.centralCharge s = L.centralChargeOfCharge (L.chargeReadout s) :=
  L.centralCharge_attractor_law s

end HorizonAttractorMicrostateLedger

/-! ## 2. Recovery witness -/

/--
Recovery witness for a horizon microstate ledger.

This is deliberately not derived from thermality or evaporation. A concrete
model must supply the decoder/readout and the equality with hidden memory.
-/
structure HorizonMemoryRecoveryWitness
    {State Charge Scalar Memory : Type*}
    (L : HorizonAttractorMicrostateLedger State Charge Scalar Memory) where
  /-- Visible/recovered memory readout. -/
  recoveredMemory :
    State → Memory

  /-- Recovery law: the visible recovered memory equals the hidden memory. -/
  recovery_law :
    ∀ s : State,
      recoveredMemory s = L.hiddenMemory s

namespace HorizonMemoryRecoveryWitness

variable
    {State Charge Scalar Memory : Type*}
    {L : HorizonAttractorMicrostateLedger State Charge Scalar Memory}

variable
    (R : HorizonMemoryRecoveryWitness L)

/-- A supplied recovery witness decodes the hidden memory. -/
theorem recoveredMemory_eq_hiddenMemory
    (s : State) :
    R.recoveredMemory s = L.hiddenMemory s :=
  R.recovery_law s

end HorizonMemoryRecoveryWitness

/-! ## 3. Thermal/KMS accounting, separate from recovery -/

/--
Thermal/KMS horizon readout socket.

This records thermality or KMS calibration as explicit model data. It does not
assert memory recovery.
-/
structure HorizonThermalLedger
    (State ThermalReadout : Type*) where
  /-- Thermal/KMS readout. -/
  thermalReadout :
    State → ThermalReadout

  /-- Predicate saying a state is thermally/KMS calibrated. -/
  IsThermal :
    State → Prop

  /-- Certificate that a selected state is thermal. -/
  thermal_certificate :
    ∀ s : State,
      IsThermal s → IsThermal s

namespace HorizonThermalLedger

variable
    {State ThermalReadout : Type*}

variable
    (T : HorizonThermalLedger State ThermalReadout)

/-- The supplied thermal/KMS certificate is available. -/
theorem thermal_valid
    {s : State}
    (hs : T.IsThermal s) :
    T.IsThermal s :=
  T.thermal_certificate s hs

end HorizonThermalLedger

/-! ## 4. Owner target -/

/--
Owner target for horizon attractor microstate accounting.

Once the ledger is supplied, entropy is determined by charge through the
installed attractor law.
-/
@[owner_target_tag]
def HorizonAttractorMicrostateOwnerTarget : Prop :=
  ∀ (State Charge Scalar Memory : Type*),
  ∀ L : HorizonAttractorMicrostateLedger State Charge Scalar Memory,
  ∀ s : State,
    L.entropyReadout s = L.entropyOfCharge (L.chargeReadout s)

/-- The owner target follows by reading the supplied attractor law. -/
theorem horizonAttractorMicrostateOwnerTarget :
    HorizonAttractorMicrostateOwnerTarget := by
  intro State Charge Scalar Memory L s
  exact L.entropyReadout_eq_entropyOfCharge s

end InfoGeometry.OperatorAlgebra.HorizonAttractorMicrostateLedger
