import InfoGeometry.OperatorAlgebra.O44PinMobiusProjective

/-!
# O(4,4) / Pin(4,4) CPT Reflection Bridge

This module records the theorem-safe correction:

* `SO(4,4)` / `Spin(4,4)` captures the even/proper split-orthogonal sector;
* parity and time reversal are reflection-type data and therefore live at the
  `O(4,4)` / `Pin(4,4)` level;
* charge conjugation is kept as a separate state-level involution.

No concrete Clifford representation, anti-linear structure, or CPT theorem is
constructed here.  This is a reflection-aware calibration layer over the
repository-owned `Pin44CoverDatum`.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra

/--
CPT reflection calibration over an existing `Pin(4,4)` cover.

The `parityPin` and `timeReversalPin` fields are explicitly required to be odd
Pin elements, because those are precisely the reflection data lost by passing
too early to the even `Spin/SO` sector.  Charge conjugation is modeled
separately as a state involution.
-/
structure CPTPin44ReflectionCalibration
    {V PinEl : Type*}
    [AddCommGroup V] [Module ℝ V]
    [Monoid PinEl]
    (Q : SplitQuadratic44 V)
    (Pin : Pin44CoverDatum (V := V) (PinEl := PinEl) Q)
    (State : Type*) where
  /-- Parity-type odd Pin representative. -/
  parityPin : PinEl

  /-- Time-reversal-type odd Pin representative. -/
  timeReversalPin : PinEl

  parity_isPin :
    Pin.isPin parityPin

  timeReversal_isPin :
    Pin.isPin timeReversalPin

  parity_odd :
    Pin.parity parityPin = PinParity.odd

  timeReversal_odd :
    Pin.parity timeReversalPin = PinParity.odd

  /--
  Certificate that the full Pin reflection socket is available in the model.
  This is intentionally explicit: the owner `Pin44CoverDatum` stores the socket
  as a proposition, and a concrete CPT model supplies the proof.
  -/
  reflectionSocketCertificate :
    Pin.odd_reflection_socket

  /-- Charge conjugation is an internal/state-level involution. -/
  chargeConjugation : State → State

  /-- Parity action on states. -/
  parityAction : State → State

  /-- Time-reversal action on states. -/
  timeReversalAction : State → State

  charge_sq :
    ∀ ψ : State, chargeConjugation (chargeConjugation ψ) = ψ

  parity_sq :
    ∀ ψ : State, parityAction (parityAction ψ) = ψ

  timeReversal_sq :
    ∀ ψ : State, timeReversalAction (timeReversalAction ψ) = ψ

  /-- The combined CPT state action, by convention `C ∘ P ∘ T`. -/
  cptAction : State → State :=
    fun ψ => chargeConjugation (parityAction (timeReversalAction ψ))

namespace CPTPin44ReflectionCalibration

variable
    {V PinEl State : Type*}
    [AddCommGroup V] [Module ℝ V]
    [Monoid PinEl]
    {Q : SplitQuadratic44 V}
    {Pin : Pin44CoverDatum (V := V) (PinEl := PinEl) Q}

variable (C : CPTPin44ReflectionCalibration Q Pin State)

/-- Parity is represented by an odd Pin element. -/
theorem parityPin_is_odd :
    Pin.parity C.parityPin = PinParity.odd :=
  C.parity_odd

/-- Time reversal is represented by an odd Pin element. -/
theorem timeReversalPin_is_odd :
    Pin.parity C.timeReversalPin = PinParity.odd :=
  C.timeReversal_odd

/-- The full Pin socket is the retained reflection lane, not merely Spin. -/
theorem odd_reflection_socket_available
    (C : CPTPin44ReflectionCalibration Q Pin State) :
    Pin.odd_reflection_socket :=
  match C with
  | { reflectionSocketCertificate := h, .. } => h

/-- Charge conjugation squares to the identity on states. -/
theorem chargeConjugation_sq
    (ψ : State) :
    C.chargeConjugation (C.chargeConjugation ψ) = ψ :=
  C.charge_sq ψ

/-- Parity squares to the identity on states. -/
theorem parityAction_sq
    (ψ : State) :
    C.parityAction (C.parityAction ψ) = ψ :=
  C.parity_sq ψ

/-- Time reversal squares to the identity on states. -/
theorem timeReversalAction_sq
    (ψ : State) :
    C.timeReversalAction (C.timeReversalAction ψ) = ψ :=
  C.timeReversal_sq ψ

end CPTPin44ReflectionCalibration

end InfoGeometry.OperatorAlgebra
