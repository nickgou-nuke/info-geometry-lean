import InfoGeometry.OperatorAlgebra.O44PinCPTReflectionBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.BogoliubovTransport

/-!
# Real `O(4,4)` / `Pin(4,4)` Hestenes-CPT owner

This module keeps the concrete split-orthogonal and Pin data owned by
`O44PinCPTReflectionBridge`.  It does not introduce generic `Type*` witness
fields for Clifford, KAN, realness, or diagonal claims.  The diagonal datum,
when present, is an explicit Cartan shadow supplied by the concrete packet.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra

structure RealHestenesO44PinCPTPacket
    {V PinEl State Bog Kpart Apart Npart CartanShadow : Type*}
    [AddCommGroup V] [Module ℝ V]
    [Monoid PinEl] [Monoid Bog] where
  splitQuadratic44 : SplitQuadratic44 V
  fullO44Transform : Orthogonal44 splitQuadratic44
  pin44Cover : Pin44CoverDatum (V := V) (PinEl := PinEl) splitQuadratic44
  cptReflection :
    CPTPin44ReflectionCalibration splitQuadratic44 pin44Cover State
  realBogoliubovTransform : Bog
  kComponent : Kpart
  aComponent : Apart
  nComponent : Npart
  cartanDiagonalShadow : CartanShadow

namespace RealHestenesO44PinCPTPacket

variable
    {V PinEl State Bog Kpart Apart Npart CartanShadow : Type*}
    [AddCommGroup V] [Module ℝ V]
    [Monoid PinEl] [Monoid Bog]

variable
    (P : RealHestenesO44PinCPTPacket
      (V := V) (PinEl := PinEl) (State := State)
      (Bog := Bog) (Kpart := Kpart) (Apart := Apart)
      (Npart := Npart) (CartanShadow := CartanShadow))

theorem parityPin_is_odd :
    P.pin44Cover.parity P.cptReflection.parityPin = PinParity.odd :=
  P.cptReflection.parityPin_is_odd

theorem timeReversalPin_is_odd :
    P.pin44Cover.parity P.cptReflection.timeReversalPin = PinParity.odd :=
  P.cptReflection.timeReversalPin_is_odd

theorem odd_reflection_socket_available :
    ∃ a : PinEl, ∃ ha : P.pin44Cover.isPin a,
      P.pin44Cover.parity a = PinParity.odd ∧
        (P.pin44Cover.cover a ha).component = O44Component.reflection :=
  P.cptReflection.odd_reflection_socket_available

theorem chargeConjugation_sq (ψ : State) :
    P.cptReflection.chargeConjugation
        (P.cptReflection.chargeConjugation ψ) = ψ :=
  P.cptReflection.chargeConjugation_sq ψ

theorem parityAction_sq (ψ : State) :
    P.cptReflection.parityAction
        (P.cptReflection.parityAction ψ) = ψ :=
  P.cptReflection.parityAction_sq ψ

theorem timeReversalAction_sq (ψ : State) :
    P.cptReflection.timeReversalAction
        (P.cptReflection.timeReversalAction ψ) = ψ :=
  P.cptReflection.timeReversalAction_sq ψ

end RealHestenesO44PinCPTPacket

end InfoGeometry.OperatorAlgebra
