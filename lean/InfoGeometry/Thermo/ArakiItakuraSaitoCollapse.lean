import InfoGeometry.Canonical.ArakiItakuraSaitoCollapse
import InfoGeometry.Prequantum.GNSBridge

/-!
# Thermodynamic Araki--Itakura--Saito facade

This file is a thin thermodynamics-facing wrapper over the canonical owner
module `InfoGeometry.Canonical.ArakiItakuraSaitoCollapse`.

It does not duplicate the canonical proofs.  Instead it packages the same
noncommutative operator Itakura--Saito/Burg collapse in a GNS-restricted form
so downstream thermodynamics imports can stay local to the `Thermo` namespace.
-/

noncomputable section

namespace InfoGeometry.Thermo.ArakiItakuraSaitoCollapse

open InfoGeometry.Prequantum.GNSBridge
open InfoGeometry.Canonical.ArakiItakuraSaitoCollapse

/--
GNS-restricted noncommutative operator collapse property.

The canonical Araki/Itakura--Saito collapse lives in the owner module; this
wrapper records that the same operatorial Bregman readout is seen through a
chosen GNS state and a noncommutative operator chart.
-/
structure GNSRestrictedOperatorCollapse
    (A Op : Type*)
    [Ring A] [Algebra ℝ A] [StarRing A] [StarModule ℝ A]
    [AddGroup Op] where
  /-- Ambient abstract GNS state. -/
  gns : AbstractGNSState A

  /-- Noncommutative Itakura--Saito/Burg operator packet. -/
  packet : NoncommutativeItakuraSaitoModel Op

  /-- Map from the ambient algebra to the noncommutative operator chart. -/
  toOperator : A → Op

  /-- Ambient Araki-style relative-entropy readout. -/
  arakiRelativeEntropy : A → A → ℝ

  /-- Two ambient states compared by the restricted Araki readout. -/
  omega : A
  phi : A

  /--
  Explicit operator collapse premise:
  the restricted Araki readout equals the noncommutative operator divergence.
  -/
  collapse :
    restrictedAraki arakiRelativeEntropy omega phi =
      packet.divergence (toOperator omega) (toOperator phi)

namespace GNSRestrictedOperatorCollapse

variable {A Op : Type*}
variable [Ring A] [Algebra ℝ A] [StarRing A] [StarModule ℝ A]
variable [AddGroup Op]
variable (C : GNSRestrictedOperatorCollapse A Op)

/-- The restricted Araki readout is the canonical noncommutative IS/Burg value. -/
theorem araki_eq_noncommutativeItakuraSaito :
    restrictedAraki C.arakiRelativeEntropy C.omega C.phi =
      C.packet.divergence (C.toOperator C.omega) (C.toOperator C.phi) :=
  C.collapse

end GNSRestrictedOperatorCollapse

end InfoGeometry.Thermo.ArakiItakuraSaitoCollapse
