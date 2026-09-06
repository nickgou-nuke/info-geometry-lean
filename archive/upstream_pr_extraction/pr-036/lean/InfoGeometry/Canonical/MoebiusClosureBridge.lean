import Mathlib.Data.Real.Basic
import InfoGeometry.Meta.Architecture

noncomputable section

/-!
# InfoGeometry.Canonical.MoebiusClosure

This file does not construct a conformal net, cyclic cohomology, Wilson-loop
path integral, or global conformal compactification theorem.  It records that a
supplied real `SL(2,R)` projective action preserves the supplied vacuum readout
and Wilson/Connes holonomy readout.

The theorem surface is intentionally only readbacks:

* the distinguished vacuum vector is fixed;
* the vacuum readout is invariant;
* the Wilson holonomy readout is invariant.
-/

namespace InfoGeometry.Canonical.MoebiusClosure

/-- A real `SL(2,R)` matrix, carried as explicit data. -/
@[rep_depth projective]
def SL2RCoordinates := ℝ × (ℝ × (ℝ × ℝ))

def SL2RDatum : Type :=
  {x : SL2RCoordinates // x.1 * x.2.2.2 - x.2.1 * x.2.2.1 = 1}

namespace SL2RDatum

abbrev a (g : SL2RDatum) : ℝ := g.1.1

abbrev b (g : SL2RDatum) : ℝ := g.1.2.1

abbrev c (g : SL2RDatum) : ℝ := g.1.2.2.1

abbrev d (g : SL2RDatum) : ℝ := g.1.2.2.2

def det_eq_one (g : SL2RDatum) : a g * d g - b g * c g = 1 := by
  exact g.2

end SL2RDatum

/--
Theorem-safe Möbius closure bridge.

`Op` is the observable/operator/cylinder object carrier.
`Hilb` is the vector/vacuum carrier.

The supplied actions are action-like maps only.  This file does not require or
assert that they are group actions, algebra automorphisms, or conformal-net
implementations.
-/
@[rep_depth projective]
structure MoebiusClosureBridgeData (Op Hilb : Type*) where
  /-- Supplied projective action on observable/operator-like objects. -/
  opAction : SL2RDatum → Op → Op

  /-- Supplied projective action on vector/vacuum-like objects. -/
  vectorAction : SL2RDatum → Hilb → Hilb

  /-- Distinguished vacuum vector/readout anchor. -/
  Omega : Hilb

  /-- Vacuum expectation / volume readout. -/
  vacuumReadout : Op → ℝ

  /-- Wilson/Connes holonomy readout. -/
  wilsonHolonomy : Op → ℝ

def MoebiusClosureBridgeLaws {Op Hilb : Type*}
    (M : MoebiusClosureBridgeData Op Hilb) : Prop :=
  (∀ g, M.vectorAction g M.Omega = M.Omega) ∧
  (∀ g A, M.vacuumReadout (M.opAction g A) = M.vacuumReadout A) ∧
  (∀ g A, M.wilsonHolonomy (M.opAction g A) = M.wilsonHolonomy A)

def MoebiusClosureBridge (Op Hilb : Type*) :=
  {M : MoebiusClosureBridgeData Op Hilb // MoebiusClosureBridgeLaws M}

namespace MoebiusClosureBridge

variable {Op Hilb : Type*}
variable (M : MoebiusClosureBridge Op Hilb)

/-- Readback: the distinguished vacuum is fixed by the supplied Möbius action. -/
@[rep_depth projective]
theorem Omega_fixed
    (g : SL2RDatum) :
    M.1.vectorAction g M.1.Omega = M.1.Omega :=
  M.2.1 g

/-- Readback: the vacuum readout is invariant under the supplied Möbius action. -/
@[rep_depth projective]
theorem vacuumReadout_moebius_invariant
    (g : SL2RDatum) (A : Op) :
    M.1.vacuumReadout (M.1.opAction g A) = M.1.vacuumReadout A :=
  M.2.2.1 g A

/-- Readback: the Wilson/Connes holonomy readout is Möbius invariant. -/
@[rep_depth projective]
theorem wilsonHolonomy_moebius_invariant
    (g : SL2RDatum) (A : Op) :
    M.1.wilsonHolonomy (M.1.opAction g A) = M.1.wilsonHolonomy A :=
  M.2.2.2 g A

end MoebiusClosureBridge

end InfoGeometry.Canonical.MoebiusClosure

end
