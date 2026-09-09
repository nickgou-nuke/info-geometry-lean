import InfoGeometry.Canonical.WeylHomogeneousReadoutBridge
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.HorizonStringDiagram

Carrier-only diagram layer for projective horizon/string pictures.

This file is deliberately not a theorem owner.  It names the diagrammatic
carriers:

* source/sink endpoints,
* global mirror pairing,
* local chiral/lightcone edge labels,
* projective/Weyl-homogeneous edge weights.

It does not assert:

* Tomita standard-form laws,
* `J` involutivity or `JMJ = M'`,
* Drazin source/sink identification,
* `u+`/`u-` edge-current laws,
* `Q² = Δ`,
* modular-flow or Hamiltonian theorems.

Those remain owned by the corresponding proving modules.
-/

namespace InfoGeometry.Canonical

open InfoGeometry.Canonical.WeylHomogeneousReadoutBridge

/-- Local diagram labels for chiral/lightcone edges. -/
inductive ChiralEdgeLabel where
  | uPlus
  | uMinus
  | neutral
deriving DecidableEq, Repr, Fintype

/--
Carrier for a projective horizon/string diagram.

`mirror` is only a diagram-level endpoint pairing.  It is not asserted to be a
Tomita conjugation or an involution in this carrier.
-/
structure HorizonStringDiagram
    (State EdgeLabel Edge Weight : Type*) where
  /-- Source endpoint of an edge. -/
  source : Edge → State

  /-- Sink endpoint of an edge. -/
  sink : Edge → State

  /-- Global mirror/twin pairing at diagram level. -/
  mirror : State → State

  /-- Local edge label, e.g. `u+`, `u-`, or a larger alphabet. -/
  edgeLabel : Edge → EdgeLabel

  /-- Projective/Weyl-homogeneous edge weight or intensity. -/
  edgeWeight : Edge → Weight

namespace HorizonStringDiagram

variable {State EdgeLabel Edge Weight : Type*}
variable (D : HorizonStringDiagram State EdgeLabel Edge Weight)

@[rep_depth operator]
theorem source_apply (e : Edge) :
    D.source e = D.source e := rfl

@[rep_depth operator]
theorem sink_apply (e : Edge) :
    D.sink e = D.sink e := rfl

@[rep_depth operator]
theorem mirror_apply (s : State) :
    D.mirror s = D.mirror s := rfl

@[rep_depth operator]
theorem edgeLabel_apply (e : Edge) :
    D.edgeLabel e = D.edgeLabel e := rfl

@[rep_depth operator]
theorem edgeWeight_apply (e : Edge) :
    D.edgeWeight e = D.edgeWeight e := rfl

end HorizonStringDiagram

/--
Horizon diagram specialized to the built-in local chiral edge alphabet.

This is still just a carrier; it does not identify labels with proved Drazin
lightcone operators.
-/
abbrev ChiralHorizonStringDiagram
    (State Edge Weight : Type*) :=
  HorizonStringDiagram State ChiralEdgeLabel Edge Weight

/--
Weyl-refined horizon/string diagram.

The homogeneous readout owns the scale law through
`WeylHomogeneousOperatorReadout`; this structure adds no new theorem.
-/
structure WeylWeightedHorizonStringDiagram
    (State EdgeLabel Edge Weight Obj : Type*) where
  diagram : HorizonStringDiagram State EdgeLabel Edge Weight
  homogeneousReadout : WeylHomogeneousOperatorReadout Obj

namespace WeylWeightedHorizonStringDiagram

variable {State EdgeLabel Edge Weight Obj : Type*}
variable (D : WeylWeightedHorizonStringDiagram State EdgeLabel Edge Weight Obj)

@[rep_depth operator]
theorem homogeneous_readout_scale (c : ℝ) (x : Obj) :
    D.homogeneousReadout.readout (D.homogeneousReadout.scale c x)
      =
    c ^ D.homogeneousReadout.weight * D.homogeneousReadout.readout x :=
  D.homogeneousReadout.readout_scale c x

end WeylWeightedHorizonStringDiagram

/--
Carrier for attaching an already-calibrated even flow object to a horizon
diagram.

The `flowGenerator` is just data here.  The statement that it is
`μ_Q • P_D Q² P_D`, or that it generates a modular flow, belongs to owner
modules such as `SuperchargeModularHamiltonianBridge`.
-/
structure HorizonStringFlowCarrier
    (State EdgeLabel Edge Weight FlowGenerator : Type*) where
  diagram : HorizonStringDiagram State EdgeLabel Edge Weight
  flowGenerator : FlowGenerator

namespace HorizonStringFlowCarrier

variable {State EdgeLabel Edge Weight FlowGenerator : Type*}
variable (C : HorizonStringFlowCarrier State EdgeLabel Edge Weight FlowGenerator)

end HorizonStringFlowCarrier

end InfoGeometry.Canonical
