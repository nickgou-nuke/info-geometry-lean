import InfoGeometry.OperatorAlgebra.NoncommutativeBogoliubovKANLift

/-!
InfoGeometry.Canonical.NoncommutativeOperatorAlgebra

Noncommutative owner-first lane for modular comparison.

This is a thin canonical re-export of
`InfoGeometry.OperatorAlgebra.NoncommutativeBogoliubovKANLift`.

The design intent is explicit: the finite diagonal charts in `ModularWeldBridge`
remain diagnostics of a chosen Bogoliubov/KAN frame, while the true owner lane
for relative modular data lives in the noncommutative operator packet.
-/

noncomputable section

namespace InfoGeometry.Canonical

open InfoGeometry.OperatorAlgebra.ConnesSpatialDerivative
open InfoGeometry.OperatorAlgebra.NoncommutativeBogoliubovKANLift

/-- Canonical-side name for the operator owner packet. -/
abbrev NoncommutativeModularOperatorLift
    (A Weight Deriv Ham Phase Core : Type*)
    [Ring A]
    [Mul Core]
    [One Deriv] [Mul Deriv]
    [Zero Ham]
    [One Phase] [Mul Phase] : Type _ :=
  InfoGeometry.OperatorAlgebra.NoncommutativeBogoliubovKANLift.NoncommutativeModularOperatorLift
    (A := A) (Weight := Weight) (Deriv := Deriv)
    (Ham := Ham) (Phase := Phase) (Core := Core)

/-- Canonical-side name for the Bogoliubov/KAN diagonal shadow packet. -/
abbrev BogoliubovKANShadowPacket
    (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (Bog Korth Asplit Nshear CartanDiag : Type*) : Type _ :=
  InfoGeometry.OperatorAlgebra.NoncommutativeBogoliubovKANLift.BogoliubovKANShadowPacket
    (E := E) (Bog := Bog) (Korth := Korth)
    (Asplit := Asplit) (Nshear := Nshear) (CartanDiag := CartanDiag)

/-- Canonical-side name for the primary operator + shadow bridge packet. -/
abbrev NoncommutativeModularToBogoliubovKANPacket
    (A Weight Deriv Ham Phase Core E Bog Korth Asplit Nshear CartanDiag : Type*)
    [Ring A]
    [Mul Core]
    [One Deriv] [Mul Deriv]
    [Zero Ham]
    [One Phase] [Mul Phase]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] : Type _ :=
  InfoGeometry.OperatorAlgebra.NoncommutativeBogoliubovKANLift.NoncommutativeModularToBogoliubovKANPacket
    (A := A) (Weight := Weight) (Deriv := Deriv)
    (Ham := Ham) (Phase := Phase) (Core := Core)
    (E := E) (Bog := Bog) (Korth := Korth)
    (Asplit := Asplit) (Nshear := Nshear) (CartanDiag := CartanDiag)

/-! Thin wrapper namespace: canonical names mirror existing operator-algebra owner facts. -/
namespace NoncommutativeModularOperatorLift

variable {A Weight Deriv Ham Phase Core : Type*}
  [Ring A] [Mul Core] [One Deriv] [Mul Deriv] [Zero Ham] [One Phase] [Mul Phase]

variable (P : NoncommutativeModularOperatorLift
  (A := A) (Weight := Weight) (Deriv := Deriv)
  (Ham := Ham) (Phase := Phase) (Core := Core))

alias connesCocycle_same_weight :=
  InfoGeometry.OperatorAlgebra.NoncommutativeBogoliubovKANLift.NoncommutativeModularOperatorLift.connesCocycle_same_weight

alias connesCocycle_chain_rule :=
  InfoGeometry.OperatorAlgebra.NoncommutativeBogoliubovKANLift.NoncommutativeModularOperatorLift.connesCocycle_chain_rule

alias spatialDerivative_same_weight :=
  InfoGeometry.OperatorAlgebra.NoncommutativeBogoliubovKANLift.NoncommutativeModularOperatorLift.spatialDerivative_same_weight

alias spatialDerivative_chain :=
  InfoGeometry.OperatorAlgebra.NoncommutativeBogoliubovKANLift.NoncommutativeModularOperatorLift.spatialDerivative_chain

alias modularFlow_one :=
  InfoGeometry.OperatorAlgebra.NoncommutativeBogoliubovKANLift.NoncommutativeModularOperatorLift.modularFlow_one

alias modularFlow_mul :=
  InfoGeometry.OperatorAlgebra.NoncommutativeBogoliubovKANLift.NoncommutativeModularOperatorLift.modularFlow_mul

/-- The canonical operator-owner packet carries an explicit noncommuting pair. -/
alias exists_noncommuting_pair :=
  InfoGeometry.OperatorAlgebra.NoncommutativeBogoliubovKANLift.NoncommutativeModularOperatorLift.exists_noncommuting_pair

/-- Type-III base integration is routed through the backend modular weight. -/
theorem typeIII_baseIntegral_eq_modularWeight_integral
    (x : A) :
    P.typeIIIIntegration.baseIntegral x =
      P.typeIIIIntegration.modularWeight.integral x :=
  rfl

/-- Type-III scalar readout is routed through the crossed-product/core trace. -/
theorem typeIII_coreTraceOfBase_eq_coreTrace_traceOfEmbedded
    (x : A) :
    P.typeIIIIntegration.coreTraceOfBase x =
      P.typeIIIIntegration.coreTrace.traceOfEmbedded x :=
  rfl

end NoncommutativeModularOperatorLift

end InfoGeometry.Canonical
