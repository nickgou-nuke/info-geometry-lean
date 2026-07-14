import InfoGeometry.OperatorAlgebra.ErlangenNet
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.OperatorAlgebra.NoetherModularFlow

Carrier layer for Fierz recombination, operator Killing fields, modular flows,
and Noether charges.

This file obeys the carrier constitution:

* structures store data only;
* law-like statements are standalone predicates/definitions;
* no structure contains a proof-carrying `Prop` field;
* no Fierz completeness, Noether theorem, Virasoro closure, or modular-flow
  theorem is asserted here.

Existing owner lanes such as `Canonical.Fierz`, `Canonical.OperatorialFierz*`,
`Canonical.KKTNoetherCharges`, and `Canonical.NoetherInference` own the actual
theorems. This module supplies a shared operator-Erlangen vocabulary.
-/

namespace NoetherModularFlow

open InfoGeometry.OperatorAlgebra.ErlangenNet

/-- Operator Killing field carrier: an infinitesimal operator/frame motion. -/
structure OperatorKillingField
    (Frame : Type*) where
  derivation : Frame → Frame

namespace OperatorKillingField

variable {Frame : Type*}
variable (K : OperatorKillingField Frame)

@[rep_depth operator]
theorem derivation_apply (A : Frame) :
    K.derivation A = K.derivation A := rfl

end OperatorKillingField

/--
Standalone predicate: a carrier derivation is linear.

This is deliberately not a field of `OperatorKillingField`.
-/
def IsLinearKillingField
    {Frame : Type*} [Add Frame] [SMul ℝ Frame]
    (K : OperatorKillingField Frame) : Prop :=
  (∀ A B : Frame, K.derivation (A + B) = K.derivation A + K.derivation B) ∧
    (∀ (c : ℝ) (A : Frame), K.derivation (c • A) = c • K.derivation A)

/--
Standalone predicate: a carrier derivation satisfies the Leibniz rule.

This is deliberately not a field of `OperatorKillingField`.
-/
def IsLeibnizKillingField
    {Frame : Type*} [Mul Frame] [Add Frame]
    (K : OperatorKillingField Frame) : Prop :=
  ∀ A B : Frame, K.derivation (A * B) = K.derivation A * B + A * K.derivation B

/-- Modular flow carrier on frames/operators. -/
structure ModularFlowCarrier
    (Frame : Type*) where
  flow : ℝ → Frame → Frame

namespace ModularFlowCarrier

variable {Frame : Type*}
variable (M : ModularFlowCarrier Frame)

@[rep_depth operator]
theorem flow_apply (t : ℝ) (A : Frame) :
    M.flow t A = M.flow t A := rfl

end ModularFlowCarrier

/--
Standalone predicate: a modular-flow carrier is a one-parameter action.

This is a predicate only, not a bundled assumption.
-/
def IsOneParameterFlow
    {Frame : Type*}
    (M : ModularFlowCarrier Frame) : Prop :=
  (∀ A : Frame, M.flow 0 A = A) ∧
    (∀ (s t : ℝ) (A : Frame), M.flow (s + t) A = M.flow s (M.flow t A))

/--
Fierz recombination channel carrier.

This stores the data of a bilinear pair and its recombination basis. It does
not assert Fierz completeness.
-/
structure FierzRecombinationChannel
    (Frame BasisIndex : Type*) where
  bilinearA : Frame
  bilinearB : Frame
  recombinationCoefficients : BasisIndex → ℝ
  recombinationBasis : BasisIndex → Frame

namespace FierzRecombinationChannel

variable {Frame BasisIndex : Type*}
variable (F : FierzRecombinationChannel Frame BasisIndex)

@[rep_depth operator]
theorem bilinearA_apply :
    F.bilinearA = F.bilinearA := rfl

@[rep_depth operator]
theorem bilinearB_apply :
    F.bilinearB = F.bilinearB := rfl

@[rep_depth operator]
theorem coefficient_apply (i : BasisIndex) :
    F.recombinationCoefficients i = F.recombinationCoefficients i := rfl

@[rep_depth operator]
theorem basis_apply (i : BasisIndex) :
    F.recombinationBasis i = F.recombinationBasis i := rfl

end FierzRecombinationChannel

/--
Formal finite recombination sum.

This is a definition, not a Fierz theorem. Any equality with a bilinear product
must be proved by an owner module.
-/
noncomputable def fierzRecombinationSum
    {Frame BasisIndex : Type*}
    [AddCommMonoid Frame] [Module ℝ Frame] [Fintype BasisIndex]
    (F : FierzRecombinationChannel Frame BasisIndex) : Frame :=
  Finset.univ.sum fun i => F.recombinationCoefficients i • F.recombinationBasis i

/--
Standalone predicate: a Fierz recombination channel is complete for a supplied
bilinear product.

This is deliberately not bundled into the carrier.
-/
def IsFierzComplete
    {Frame BasisIndex : Type*}
    [AddCommMonoid Frame] [Module ℝ Frame] [Fintype BasisIndex]
    (bilinearProduct : Frame → Frame → Frame)
    (F : FierzRecombinationChannel Frame BasisIndex) : Prop :=
  bilinearProduct F.bilinearA F.bilinearB = fierzRecombinationSum F

/-- Noether charge carrier: an observable/charge and a readout map. -/
structure OperatorNoetherCharge
    (Frame Readout : Type*) where
  chargeObservable : Frame
  readoutMap : Frame → Readout

namespace OperatorNoetherCharge

variable {Frame Readout : Type*}
variable (Q : OperatorNoetherCharge Frame Readout)

@[rep_depth operator]
theorem chargeObservable_apply :
    Q.chargeObservable = Q.chargeObservable := rfl

@[rep_depth operator]
theorem readout_apply (A : Frame) :
    Q.readoutMap A = Q.readoutMap A := rfl

end OperatorNoetherCharge

/--
Standalone predicate: an operator is invariant under a Killing field.

This is the Noether-charge condition in carrier language.
-/
def IsNoetherInvariant
    {Frame : Type*} [Zero Frame]
    (K : OperatorKillingField Frame) (A : Frame) : Prop :=
  K.derivation A = 0

/-- Definitional readback of the Noether-invariant predicate. -/
@[rep_depth operator]
theorem isNoetherInvariant_iff_derivation_eq_zero
    {Frame : Type*} [Zero Frame]
    (K : OperatorKillingField Frame) (A : Frame) :
    IsNoetherInvariant K A ↔ K.derivation A = 0 :=
  Iff.rfl

/-- Standalone predicate: a Noether charge is conserved by a Killing field. -/
def IsConservedNoetherCharge
    {Frame Readout : Type*} [Zero Frame]
    (K : OperatorKillingField Frame)
    (Q : OperatorNoetherCharge Frame Readout) : Prop :=
  IsNoetherInvariant K Q.chargeObservable

/-- Definitional readback of charge conservation. -/
@[rep_depth operator]
theorem isConservedNoetherCharge_iff
    {Frame Readout : Type*} [Zero Frame]
    (K : OperatorKillingField Frame)
    (Q : OperatorNoetherCharge Frame Readout) :
    IsConservedNoetherCharge K Q ↔ K.derivation Q.chargeObservable = 0 :=
  Iff.rfl

/--
Carrier tying an Erlangen sectorization, modular flow, Killing field, and
Noether charge together.

No compatibility theorem is stored here.
-/
structure ModularNoetherErlangenCarrier
    (Alg Frame Sym Symbol Label Readout : Type*) where
  net : IteratedObservableSectorization Alg Frame Sym Symbol Label
  modularFlow : ModularFlowCarrier Frame
  killingField : OperatorKillingField Frame
  charge : OperatorNoetherCharge Frame Readout

namespace ModularNoetherErlangenCarrier

variable {Alg Frame Sym Symbol Label Readout : Type*}
variable (C : ModularNoetherErlangenCarrier Alg Frame Sym Symbol Label Readout)

@[rep_depth operator]
theorem net_apply :
    C.net = C.net := rfl

@[rep_depth operator]
theorem modularFlow_apply :
    C.modularFlow = C.modularFlow := rfl

@[rep_depth operator]
theorem killingField_apply :
    C.killingField = C.killingField := rfl

@[rep_depth operator]
theorem charge_apply :
    C.charge = C.charge := rfl

end ModularNoetherErlangenCarrier

end NoetherModularFlow
