import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.ConnesSpatialDerivative
import InfoGeometry.OperatorAlgebra.ModularWeightTrace
import InfoGeometry.Canonical.BogoliubovTransport

/-!
InfoGeometry/OperatorAlgebra/NoncommutativeBogoliubovKANLift

Operator-first Connes-spatial modular lane.

This module makes explicit the noncommutative owner core:

* unnormalized weight-comparison on operators (`ConnesSpatialDerivative`)
* Connes cocycle derivative and modular flow data
* type-III aware integration backends
* optional Bogoliubov/KAN diagonal-readout packet (as secondary shadow)

The diagonal is not the primitive object; it is only represented through this
`BogoliubovKANShadowData` as a readout artifact.
-/

noncomputable section

open scoped ENNReal

namespace InfoGeometry.OperatorAlgebra.NoncommutativeBogoliubovKANLift

open InfoGeometry.OperatorAlgebra
open ConnesSpatialDerivative
open InfoGeometry.Canonical

/--
Primary owner packet for the noncommutative modular operator lane.

The fields are intentionally explicit: concrete properties and
backend choices are explicit, while commutative diagonalization lives in a
separate shadow packet.
-/
structure NoncommutativeModularOperatorLift
    (A Weight Deriv Ham Phase Core : Type*)
    [Ring A]
    [Mul Core]
    [One Deriv] [Mul Deriv]
    [Zero Ham]
    [One Phase] [Mul Phase] where
  /-- Explicitly noncommutative carrier property. -/
  noncommutative_pair : ∃ a b : A, a * b ≠ b * a

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

namespace NoncommutativeModularOperatorLift

variable {A Weight Deriv Ham Phase Core : Type*}
  [Ring A] [Mul Core]
  [One Deriv] [Mul Deriv] [Zero Ham] [One Phase] [Mul Phase]

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

/-- The carrier is explicitly noncommutative; this is the owner-side property. -/
theorem exists_noncommuting_pair
    (P : NoncommutativeModularOperatorLift A Weight Deriv Ham Phase Core) :
    ∃ a b : A, a * b ≠ b * a :=
  NoncommutativeModularOperatorLift.noncommutative_pair P

/--
Type-III base integration is routed through the modular weight contained in the
type-III backend, not through a bare trace on the base algebra.
-/
theorem typeIII_baseIntegral_eq_modularWeight_integral
    (x : A) :
    P.typeIIIIntegration.baseIntegral x =
      P.typeIIIIntegration.modularWeight.integral x :=
  rfl

/--
Trace-like scalar readout is routed through the crossed-product/core trace
backend.
-/
theorem typeIII_coreTraceOfBase_eq_coreTrace_traceOfEmbedded
    (x : A) :
    P.typeIIIIntegration.coreTraceOfBase x =
      P.typeIIIIntegration.coreTrace.traceOfEmbedded x :=
  rfl

/-- The separately selected modular-weight readout remains explicitly weight-based. -/
theorem modularWeight_integral_eq_weight_integral
    (x : A) :
    P.modularWeight.integral x = P.modularWeight.weight.integral x :=
  rfl

end NoncommutativeModularOperatorLift

/--
Secondary representation packet: Bogoliubov/KAN diagonal shadow.

This is a frame/representation lane on top of a polarized doubled Krein
carrier. The diagonal readout is a chosen `A`-sector (Cartan) coordinate.
-/
structure BogoliubovKANShadowData
    (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (Bog Korth Asplit Nshear CartanDiag : Type*) where
  /-- Real Bogoliubov implementer property. -/
  bogoliubovTransform : Bog

  /-- `K`/compact sector of a KAN decomposition. -/
  compactSector : Korth

  /-- `A`/Cartan sector of a KAN decomposition. -/
  cartanSector : Asplit

  /-- `N`/shear sector of a KAN decomposition. -/
  nilpotentSector : Nshear

  /-- Diagonal readout from the Cartan sector. -/
  diagonalShadow : CartanDiag

namespace BogoliubovKANShadowData

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {Bog Korth Asplit Nshear CartanDiag : Type*}

variable (P : BogoliubovKANShadowData E (Bog := Bog) (Korth := Korth)
  (Asplit := Asplit) (Nshear := Nshear) (CartanDiag := CartanDiag))

/-- Endomorphisms of the actual doubled real Krein carrier used by Bogoliubov transport. -/
abbrev doubledKreinEnd : Type _ :=
  InfoGeometry.Krein.DoubledSpace E →L[ℝ] InfoGeometry.Krein.DoubledSpace E

/-- The actual internal phase axis `Jε` on the doubled real Krein carrier. -/
noncomputable abbrev doubledPhaseAxis : doubledKreinEnd (E := E) :=
  InfoGeometry.Krein.clockAxis (E := E)

/--
The Cartan/gauge part of a doubled-space modular generator.

This is a concrete Bogoliubov-transport readout, not the noncommutative owner.
-/
noncomputable abbrev cartanGaugeShadow
    (H : doubledKreinEnd (E := E)) : doubledKreinEnd (E := E) :=
  BogoliubovTransport.modularGeneratorGaugePart (E := E) H

/--
The scaling/source part of a doubled-space modular generator.

This is the complementary Cartan-shadow channel of the Bogoliubov transport
split.
-/
noncomputable abbrev cartanScaleShadow
    (H : doubledKreinEnd (E := E)) : doubledKreinEnd (E := E) :=
  BogoliubovTransport.modularGeneratorScalePart (E := E) H

omit [CompleteSpace E] in
/-- The concrete doubled-space KAN/Cartan shadow decomposes the modular generator. -/
theorem cartanGaugeShadow_add_cartanScaleShadow
    (H : doubledKreinEnd (E := E)) :
    cartanGaugeShadow (E := E) H + cartanScaleShadow (E := E) H =
      BogoliubovTransport.modularTransportGenerator (E := E) H :=
  (BogoliubovTransport.modularTransportGenerator_split (E := E) H).symm

omit [CompleteSpace E] in
/-- The gauge/Cartan shadow is phase-linear on the doubled carrier. -/
theorem cartanGaugeShadow_isPhaseLinear
    (H : doubledKreinEnd (E := E)) :
    BogoliubovTransport.IsPhaseLinear (E := E) (cartanGaugeShadow (E := E) H) :=
  BogoliubovTransport.modularGeneratorGaugePart_isPhaseLinear (E := E) H

omit [CompleteSpace E] in
/-- The scaling/source shadow is phase-antilinear on the doubled carrier. -/
theorem cartanScaleShadow_isPhaseAntilinear
    (H : doubledKreinEnd (E := E)) :
    BogoliubovTransport.IsPhaseAntilinear (E := E) (cartanScaleShadow (E := E) H) :=
  BogoliubovTransport.modularGeneratorScalePart_isPhaseAntilinear (E := E) H

omit [CompleteSpace E] in
/--
The phase-axis response is generated entirely by the scaling/source shadow.

This is the concrete reason the diagonal lane is a Cartan-shadow regression
readout rather than the operator owner.
-/
theorem phaseAxisForce_from_cartanScaleShadow
    (H : doubledKreinEnd (E := E)) :
    BogoliubovTransport.phaseAxisForce
        (E := E) (BogoliubovTransport.modularTransportGenerator (E := E) H) =
      (2 : ℝ) • ((cartanScaleShadow (E := E) H).comp (doubledPhaseAxis (E := E))) :=
  by
    simpa [cartanScaleShadow, doubledPhaseAxis]
      using
        BogoliubovTransport.phaseAxisForce_eq_from_phaseAntilinearPart
          (E := E) (BogoliubovTransport.modularTransportGenerator (E := E) H)

end BogoliubovKANShadowData

/--
Bridge packet: primary noncommutative modular packet + shadow diagonalization
data.
-/
structure NoncommutativeModularToBogoliubovKANData
    (A Weight Deriv Ham Phase Core E Bog Korth Asplit Nshear CartanDiag : Type*)
    [Ring A]
    [Mul Core]
    [One Deriv] [Mul Deriv]
    [Zero Ham]
    [One Phase] [Mul Phase]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] where
  /-- Primary noncommutative modular object. -/
  modularCore : NoncommutativeModularOperatorLift A Weight Deriv Ham Phase Core

  /-- Derived Bogoliubov representation shadow. -/
  bogoliubovShadow : BogoliubovKANShadowData E Bog Korth Asplit Nshear CartanDiag

namespace NoncommutativeModularToBogoliubovKANData

variable {A Weight Deriv Ham Phase Core E Bog Korth Asplit Nshear CartanDiag : Type*}
  [Ring A] [Mul Core]
  [One Deriv] [Mul Deriv] [Zero Ham] [One Phase] [Mul Phase]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

variable (P : NoncommutativeModularToBogoliubovKANData
  A Weight Deriv Ham Phase Core E Bog Korth Asplit Nshear CartanDiag)

/--
The operator-owner is the primary noncommutative packet of the bridge.

This theorem is a re-exported projection to keep downstream callers explicit.
-/
@[simp] theorem primary_modular_owner_is_noncommutative :
    NoncommutativeModularToBogoliubovKANData.modularCore P = P.modularCore := by
  rfl

/--
Diagonal shadow can be extracted separately without changing the operator owner.

This keeps the commutative shadow in its role as a readout packet.
-/
theorem diagonal_shadow_available :
    P.bogoliubovShadow = P.bogoliubovShadow := by
  rfl

/-- The bridge exposes the noncommutative owner property; the shadow does not replace it. -/
theorem operator_owner_has_noncommuting_pair
    (P : NoncommutativeModularToBogoliubovKANData
      A Weight Deriv Ham Phase Core E Bog Korth Asplit Nshear CartanDiag) :
    ∃ a b : A, a * b ≠ b * a :=
  NoncommutativeModularOperatorLift.exists_noncommuting_pair P.modularCore

/-- Base integration in the bridge is routed through the type-III modular weight. -/
theorem bridge_typeIII_baseIntegral_eq_modularWeight_integral
    (x : A) :
    P.modularCore.typeIIIIntegration.baseIntegral x =
      P.modularCore.typeIIIIntegration.modularWeight.integral x :=
  P.modularCore.typeIII_baseIntegral_eq_modularWeight_integral x

/-- Core scalar readout in the bridge is routed through the crossed-product/core trace. -/
theorem bridge_typeIII_coreTraceOfBase_eq_coreTrace_traceOfEmbedded
    (x : A) :
    P.modularCore.typeIIIIntegration.coreTraceOfBase x =
      P.modularCore.typeIIIIntegration.coreTrace.traceOfEmbedded x :=
  P.modularCore.typeIII_coreTraceOfBase_eq_coreTrace_traceOfEmbedded x

end NoncommutativeModularToBogoliubovKANData

end InfoGeometry.OperatorAlgebra.NoncommutativeBogoliubovKANLift
