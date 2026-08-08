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
* optional recovery property saying hidden memory is visible under a supplied
  decoding channel.

Thermal/KMS readouts are kept separate from recovery: a thermal property by
itself does not decode hidden memory.
-/

import Mathlib.Tactic

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

/-- Lemma 1: equal charge readouts give equal entropy-of-charge values. -/
theorem entropyOfCharge_eq_of_chargeReadout_eq
    {s₁ s₂ : State}
    (hcharge : L.chargeReadout s₁ = L.chargeReadout s₂) :
    L.entropyOfCharge (L.chargeReadout s₁) =
      L.entropyOfCharge (L.chargeReadout s₂) := by
  rw [hcharge]

/-- Lemma 2: equal charge readouts give equal central-charge-of-charge values. -/
theorem centralChargeOfCharge_eq_of_chargeReadout_eq
    {s₁ s₂ : State}
    (hcharge : L.chargeReadout s₁ = L.chargeReadout s₂) :
    L.centralChargeOfCharge (L.chargeReadout s₁) =
      L.centralChargeOfCharge (L.chargeReadout s₂) := by
  rw [hcharge]

/-- Lemma 3: entropy readout is constant on charge fibers. -/
theorem entropyReadout_eq_of_chargeReadout_eq
    {s₁ s₂ : State}
    (hcharge : L.chargeReadout s₁ = L.chargeReadout s₂) :
    L.entropyReadout s₁ = L.entropyReadout s₂ := by
  rw [L.entropyReadout_eq_entropyOfCharge s₁]
  rw [L.entropyReadout_eq_entropyOfCharge s₂]
  exact L.entropyOfCharge_eq_of_chargeReadout_eq hcharge

/-- Lemma 4: central-charge readout is constant on charge fibers. -/
theorem centralCharge_eq_of_chargeReadout_eq
    {s₁ s₂ : State}
    (hcharge : L.chargeReadout s₁ = L.chargeReadout s₂) :
    L.centralCharge s₁ = L.centralCharge s₂ := by
  rw [L.centralCharge_eq_centralChargeOfCharge s₁]
  rw [L.centralCharge_eq_centralChargeOfCharge s₂]
  exact L.centralChargeOfCharge_eq_of_chargeReadout_eq hcharge

/-- Theorem: attractor readouts are constant on charge fibers. -/
theorem attractorReadouts_eq_of_chargeReadout_eq
    {s₁ s₂ : State}
    (hcharge : L.chargeReadout s₁ = L.chargeReadout s₂) :
    L.entropyReadout s₁ = L.entropyReadout s₂ ∧
      L.centralCharge s₁ = L.centralCharge s₂ := by
  exact ⟨L.entropyReadout_eq_of_chargeReadout_eq hcharge,
    L.centralCharge_eq_of_chargeReadout_eq hcharge⟩

end HorizonAttractorMicrostateLedger

/-! ## 2. Recovery property -/

/--
Recovery property for a horizon microstate ledger.

This is deliberately not derived from thermality or evaporation. A concrete
model must supply the decoder/readout and the equality with hidden memory.
-/
abbrev HorizonMemoryRecoveryWitness
    {State Charge Scalar Memory : Type*}
    (L : HorizonAttractorMicrostateLedger State Charge Scalar Memory) :=
  { recoveredMemory : State → Memory // recoveredMemory = L.hiddenMemory }

namespace HorizonMemoryRecoveryWitness

variable
    {State Charge Scalar Memory : Type*}
    {L : HorizonAttractorMicrostateLedger State Charge Scalar Memory}

variable
    (R : HorizonMemoryRecoveryWitness L)

/-- Visible/recovered memory readout of the native equality subtype. -/
def recoveredMemory : State → Memory :=
  R.1

/-- Recovery law derived from the subtype equality. -/
theorem recovery_law :
    ∀ s : State,
      R.recoveredMemory s = L.hiddenMemory s := by
  intro s
  change R.1 s = L.hiddenMemory s
  rw [R.2]

/-- A supplied recovery property decodes the hidden memory. -/
theorem recoveredMemory_eq_hiddenMemory
    (s : State) :
    R.recoveredMemory s = L.hiddenMemory s :=
  R.recovery_law s

/-- Lemma 5: recovery transports hidden-memory equality to recovered-memory equality. -/
theorem recoveredMemory_eq_of_hiddenMemory_eq
    {s₁ s₂ : State}
    (hmem : L.hiddenMemory s₁ = L.hiddenMemory s₂) :
    R.recoveredMemory s₁ = R.recoveredMemory s₂ := by
  rw [R.recoveredMemory_eq_hiddenMemory s₁]
  rw [R.recoveredMemory_eq_hiddenMemory s₂]
  exact hmem

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


namespace HorizonThermalLedger

variable
    {State ThermalReadout : Type*}

variable
    (T : HorizonThermalLedger State ThermalReadout)

end HorizonThermalLedger

end InfoGeometry.OperatorAlgebra.HorizonAttractorMicrostateLedger
