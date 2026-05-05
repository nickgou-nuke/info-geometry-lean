/-!
InfoGeometry.Canonical.NoncommutativeOperatorAlgebra

Noncommutative owner-first lane for modular comparison.

This is a thin canonical re-export of
`InfoGeometry.OperatorAlgebra.NoncommutativeBogoliubovKANLift`.

The design intent is explicit: the finite diagonal charts in `ModularWeldBridge`
remain diagnostics of a chosen Bogoliubov/KAN frame, while the true owner lane
for relative modular data lives in the noncommutative operator packet.
-/

import InfoGeometry.OperatorAlgebra.NoncommutativeBogoliubovKANLift

noncomputable section

namespace InfoGeometry.Canonical

open InfoGeometry.OperatorAlgebra.ConnesSpatialDerivative
open InfoGeometry.OperatorAlgebra.NoncommutativeBogoliubovKANLift

/-- Canonical-side name for the operator owner packet. -/
abbrev NoncommutativeModularOperatorLift
    (A Weight Deriv Ham Phase Core : Type*)
    [Ring A]
    [One Deriv] [Mul Deriv]
    [Zero Ham]
    [One Phase] [Mul Phase] : Type* :=
  InfoGeometry.OperatorAlgebra.NoncommutativeBogoliubovKANLift.NoncommutativeModularOperatorLift
    (A := A) (Weight := Weight) (Deriv := Deriv)
    (Ham := Ham) (Phase := Phase) (Core := Core)

/-- Canonical-side name for the Bogoliubov/KAN diagonal shadow packet. -/
abbrev BogoliubovKANShadowPacket
    (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (Bog Korth Asplit Nshear CartanDiag : Type*) : Type* :=
  InfoGeometry.OperatorAlgebra.NoncommutativeBogoliubovKANLift.BogoliubovKANShadowPacket
    (E := E) (Bog := Bog) (Korth := Korth)
    (Asplit := Asplit) (Nshear := Nshear) (CartanDiag := CartanDiag)

/-- Canonical-side name for the primary operator + shadow bridge packet. -/
abbrev NoncommutativeModularToBogoliubovKANPacket
    (A Weight Deriv Ham Phase Core E Bog Korth Asplit Nshear CartanDiag : Type*)
    [Ring A]
    [One Deriv] [Mul Deriv]
    [Zero Ham]
    [One Phase] [Mul Phase]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] : Type* :=
  InfoGeometry.OperatorAlgebra.NoncommutativeBogoliubovKANLift.NoncommutativeModularToBogoliubovKANPacket
    (A := A) (Weight := Weight) (Deriv := Deriv)
    (Ham := Ham) (Phase := Phase) (Core := Core)
    (E := E) (Bog := Bog) (Korth := Korth)
    (Asplit := Asplit) (Nshear := Nshear) (CartanDiag := CartanDiag)

/-- Thin wrapper namespace: canonical names mirror existing operator-algebra owner facts. -/
namespace NoncommutativeModularOperatorLift

variable {A Weight Deriv Ham Phase Core : Type*}
  [Ring A] [One Deriv] [Mul Deriv] [Zero Ham] [One Phase] [Mul Phase]

variable (P : NoncommutativeModularOperatorLift
  (A := A) (Weight := Weight) (Deriv := Deriv)
  (Ham := Ham) (Phase := Phase) (Core := Core))

theorem connesCocycle_same_weight
    (φ : Weight)
    (t : ℝ) :
    P.connesCocycle.cocycle φ φ t = 1 := by
  exact P.connesCocycle.same_weight_apply φ t

theorem connesCocycle_chain_rule
    (φ ψ η : Weight)
    (t : ℝ) :
    P.connesCocycle.cocycle φ ψ t * P.connesCocycle.cocycle ψ η t =
      P.connesCocycle.cocycle φ η t :=
  P.connesCocycle.chain_rule_apply φ ψ η t

theorem spatialDerivative_same_weight
    (φ : Weight) :
    P.spatialDerivative.spatialDerivative φ φ = 1 := by
  exact P.spatialDerivative.same_weight_apply φ

theorem spatialDerivative_chain
    (φ ψ η : Weight) :
    P.spatialDerivative.spatialDerivative φ ψ * P.spatialDerivative.spatialDerivative ψ η =
      P.spatialDerivative.spatialDerivative φ η := by
  exact P.spatialDerivative.chain_rule_apply φ ψ η

theorem modularFlow_one
    (t : ℝ) :
    P.modularFlow.flow t (1 : A) = 1 := by
  exact P.modularFlow.flow_one_apply t

theorem modularFlow_mul
    (t : ℝ) (x y : A) :
    P.modularFlow.flow t (x * y) =
      P.modularFlow.flow t x * P.modularFlow.flow t y := by
  exact P.modularFlow.flow_mul_apply t x y

end NoncommutativeModularOperatorLift

end InfoGeometry.Canonical
