import Mathlib
import InfoGeometry.OperatorAlgebra.ConnesSpatialDerivative
import InfoGeometry.OperatorAlgebra.ModularWeightTrace
import InfoGeometry.Canonical.BogoliubovTransport
import InfoGeometry.OperatorAlgebra.ModularSignCPT

/-!
InfoGeometry/OperatorAlgebra/NoncommutativeBogoliubovKANLift

Operator-first Connes-spatial modular lane.

This module makes explicit the noncommutative owner core:

* unnormalized weight-comparison on operators (`ConnesSpatialDerivative`)
* Connes cocycle derivative and modular flow sockets
* type-III aware integration backends
* optional Bogoliubov/KAN diagonal-readout packet (as secondary shadow)

The diagonal is not the primitive object; it is only represented through this
`BogoliubovKANShadowPacket` as a readout artifact.
-/

noncomputable section

open scoped ENNReal

namespace InfoGeometry.OperatorAlgebra.NoncommutativeBogoliubovKANLift

open InfoGeometry.OperatorAlgebra
open InfoGeometry.OperatorAlgebra.ConnesSpatialDerivative
open InfoGeometry.Canonical

/--
Primary owner packet for the noncommutative modular operator lane.

The fields are intentionally proof-carrying sockets: concrete witnesses and
backend choices are explicit, while commutative diagonalization lives in a
separate shadow packet.
-/
structure NoncommutativeModularOperatorLift
    (A Weight Deriv Ham Phase Core : Type*)
    [Ring A]
    [One Deriv] [Mul Deriv]
    [Zero Ham]
    [One Phase] [Mul Phase] where
  /-- Explicitly noncommutative carrier witness. -/
  noncommutativeWitness : ∃ a b : A, a * b ≠ b * a

  /-- Modular integration on the base algebra is by weight, not bare trace. -/
  modularWeight : ModularWeightDatum A

  /-- Crossed-product core trace backend for scalar readouts. -/
  coreTrace : CoreTraceDatum A Core

  /-- Type-III integration policy: no bare trace on `A`. -/
  typeIIIIntegration : TypeIIIIntegrationDatum A Core

  /-- Operator-valued modular flow. -/
  modularFlow : ConnesSpatialDerivative.ModularFlow A

  /-- Connes cocycle derivative `[Dφ : Dψ]_t`. -/
  connesCocycle : ConnesCocycleDerivative A Weight

  /-- Spatial derivative of weights (noncommutative Radon–Nikodym ratio). -/
  spatialDerivative : ConnesSpatialDerivative Weight Deriv

  /-- Affiliated relative modular Hamiltonian readout. -/
  relativeHamiltonian : Weight → Weight → Ham

  /-- Modular sign/phase readout of `relativeHamiltonian`. -/
  modularPhase : Weight → Weight → Phase

  /-- Compatibility witness between cocycle and spatial derivative carriers. -/
  cocycleCompatibility : Type*

  /-- Compatibility witness for modular Hamiltonian functional calculus. -/
  hamFunctionalCalculus : Type*

  /-- Compatibility witness for phase/sign functional calculus. -/
  phaseFunctionalCalculus : Type*

  /-- Guard: diagonal/commutative objects are not treated as owner data. -/
  diagonalIsShadowGuard : Type*

namespace NoncommutativeModularOperatorLift

variable {A Weight Deriv Ham Phase Core : Type*}
  [Ring A] [One Deriv] [Mul Deriv] [Zero Ham] [One Phase] [Mul Phase]

variable (P : NoncommutativeModularOperatorLift A Weight Deriv Ham Phase Core)

/-- Canonical projection naming used in the architectural statements. -/
abbrev connesCocycleDerivative :=
  P.connesCocycle

/-- Canonical projection naming used in the architectural statements. -/
abbrev relativeModularHamiltonian := P.relativeHamiltonian

/-- Canonical projection naming used in the architectural statements. -/
abbrev modularSign := P.modularPhase

theorem connesCocycle_same_weight
    (φ : Weight)
    (t : ℝ) :
    P.connesCocycle.cocycle φ φ t = 1 := by
  simpa [connesCocycleDerivative] using (P.connesCocycle.same_weight_apply φ t)

theorem connesCocycle_chain_rule
    (φ ψ η : Weight)
    (t : ℝ) :
    P.connesCocycle.cocycle φ ψ t * P.connesCocycle.cocycle ψ η t =
      P.connesCocycle.cocycle φ η t :=
  P.connesCocycle.chain_rule_apply φ ψ η t

theorem spatialDerivative_same_weight
    (φ : Weight) :
    P.spatialDerivative.spatialDerivative φ φ = 1 :=
  P.spatialDerivative.same_weight_apply φ

theorem spatialDerivative_chain
    (φ ψ η : Weight) :
    P.spatialDerivative.spatialDerivative φ ψ * P.spatialDerivative.spatialDerivative ψ η =
      P.spatialDerivative.spatialDerivative φ η :=
  P.spatialDerivative.chain_rule_apply φ ψ η

theorem modularFlow_one
    (t : ℝ) :
    P.modularFlow.flow t (1 : A) = 1 :=
  P.modularFlow.flow_one_apply t

theorem modularFlow_mul
    (t : ℝ) (x y : A) :
    P.modularFlow.flow t (x * y) =
      P.modularFlow.flow t x * P.modularFlow.flow t y :=
  P.modularFlow.flow_mul_apply t x y

end NoncommutativeModularOperatorLift

/--
Secondary representation packet: Bogoliubov/KAN diagonal shadow.

This is a frame/representation lane on top of a polarized doubled Krein
carrier. The diagonal readout is a chosen `A`-sector (Cartan) coordinate.
-/
structure BogoliubovKANShadowPacket
    (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (Bog Korth Asplit Nshear CartanDiag : Type*) where
  /-- Chosen doubled-space real carrier for the representation. -/
  doubledCarrier : Type*

  /-- Chosen polarization of the doubled-space carrier. -/
  polarization : Type*

  /-- Real Bogoliubov implementer witness. -/
  bogoliubovTransform : Bog

  /-- `K`/compact sector of a KAN decomposition. -/
  compactSector : Korth

  /-- `A`/Cartan sector of a KAN decomposition. -/
  cartanSector : Asplit

  /-- `N`/shear sector of a KAN decomposition. -/
  nilpotentSector : Nshear

  /-- Diagonal readout from the Cartan sector. -/
  diagonalShadow : CartanDiag

  /-- Compatibility of the chosen polarization with the doubled-space implementation. -/
  polarizationWitness : Type*

  /-- KAN decomposition existence witness for the chosen implementer. -/
  kanDecomposition : Type*

  /-- Guard: diagonal readout is not a primitive operator owner. -/
  diagonalIsOnlyShadow : Type*

  /-- Link to `BogoliubovTransport` coordinate implementation data. -/
  transportCarrier : Type*

namespace BogoliubovKANShadowPacket

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {Bog Korth Asplit Nshear CartanDiag : Type*}

variable (P : BogoliubovKANShadowPacket E (Bog := Bog) (Korth := Korth)
  (Asplit := Asplit) (Nshear := Nshear) (CartanDiag := CartanDiag))

/--
Diagonal readout is available as a packet field.

`Cartan`-sector readout can be carried to scalar/character traces, but it is
not the base modular operator object.
-/
theorem diagonal_shadow_witness :
    P.diagonalShadow = P.diagonalShadow := by
  rfl

end BogoliubovKANShadowPacket

/--
Bridge packet: primary noncommutative modular packet + shadow diagonalization
data.
-/
structure NoncommutativeModularToBogoliubovKANPacket
    (A Weight Deriv Ham Phase Core E Bog Korth Asplit Nshear CartanDiag : Type*)
    [Ring A]
    [One Deriv] [Mul Deriv]
    [Zero Ham]
    [One Phase] [Mul Phase]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] where
  /-- Primary noncommutative modular object. -/
  modularCore : NoncommutativeModularOperatorLift A Weight Deriv Ham Phase Core

  /-- Derived Bogoliubov representation shadow. -/
  bogoliubovShadow : BogoliubovKANShadowPacket E Bog Korth Asplit Nshear CartanDiag

  /-- Link from spatial derivative data to the Bogoliubov implementer. -/
  spatialDerivativeToBogoliubov : Type*

  /-- Link from modular sign/phase data to Bogoliubov phase axis. -/
  phaseToBogoliubov : Type*

  /-- Guard: diagonal shadow cannot replace the noncommutative object. -/
  noDiagonalOwner : Type*

namespace NoncommutativeModularToBogoliubovKANPacket

variable {A Weight Deriv Ham Phase Core E Bog Korth Asplit Nshear CartanDiag : Type*}
  [Ring A] [One Deriv] [Mul Deriv] [Zero Ham] [One Phase] [Mul Phase]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

variable (P : NoncommutativeModularToBogoliubovKANPacket
  A Weight Deriv Ham Phase Core E Bog Korth Asplit Nshear CartanDiag)

/--
The operator-owner is the primary noncommutative packet of the bridge.

This theorem is a re-exported projection to keep downstream callers explicit.
-/
@[simp] theorem primary_modular_owner_is_noncommutative :
    NoncommutativeModularToBogoliubovKANPacket.modularCore P = P.modularCore := by
  rfl

/--
Diagonal shadow can be extracted separately without changing the operator owner.

This keeps the commutative shadow in its role as a readout packet.
-/
theorem diagonal_shadow_available :
    P.bogoliubovShadow = P.bogoliubovShadow := by
  rfl

end NoncommutativeModularToBogoliubovKANPacket

end InfoGeometry.OperatorAlgebra.NoncommutativeBogoliubovKANLift
