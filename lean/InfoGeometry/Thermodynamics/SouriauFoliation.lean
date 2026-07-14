/-
InfoGeometry/Thermodynamics/SouriauFoliation.lean

Witness-gated Souriau foliation sidecar.

This module packages the finite/projective shadow of the Souriau picture in
which reversible modular motion stays on an entropy/Weyl leaf, while a
dissipative JKO-style step is supplied as a transverse law.

It does not construct coadjoint orbits, symplectic forms, KMS states, Tomita-
Takesaki modular groups, or global Souriau thermodynamics. Those claims remain
behind explicit witness fields or the existing canonical coadjoint-orbit
theorem packets.
-/

import InfoGeometry.OperatorAlgebra.MobiusClosureFixedPoints
import InfoGeometry.Thermodynamics.SouriauTemperatureProjective

noncomputable section

namespace InfoGeometry.Thermodynamics.SouriauFoliation

open InfoGeometry.OperatorAlgebra.MobiusClosureFixedPoints
open InfoGeometry.Thermodynamics

/-! ## 1. Abstract Souriau leaves -/

/-- A finite/projective Souriau leaf.

The leaf is represented only by the data needed by the current sidecar:
membership, an entropy readout, and a Weyl-scale readout which are constant on
the carrier. This is not a construction of a coadjoint orbit or a symplectic
form. -/
structure SymplecticLeaf
    (State : Type*) where
  /-- States belonging to the leaf. -/
  carrier : Set State

  /-- Entropy/action readout. -/
  entropyReadout : State → ℝ

  /-- Weyl/conformal scale readout. -/
  weylScaleReadout : State → ℝ

  /-- Leaf entropy value. -/
  leafEntropy : ℝ

  /-- Leaf Weyl-scale value. -/
  leafWeylScale : ℝ

  /-- Entropy is constant on the leaf. -/
  entropy_constant :
    ∀ ⦃x : State⦄, x ∈ carrier → entropyReadout x = leafEntropy

  /-- Weyl scale is constant on the leaf. -/
  weylScale_constant :
    ∀ ⦃x : State⦄, x ∈ carrier → weylScaleReadout x = leafWeylScale

namespace SymplecticLeaf

variable {State : Type*}
variable (L : SymplecticLeaf State)

/-- Two states on the same leaf have the same entropy readout. -/
theorem entropy_eq_of_mem
    {x y : State}
    (hx : x ∈ L.carrier)
    (hy : y ∈ L.carrier) :
    L.entropyReadout x = L.entropyReadout y := by
  rw [L.entropy_constant hx, L.entropy_constant hy]

/-- Two states on the same leaf have the same Weyl-scale readout. -/
theorem weylScale_eq_of_mem
    {x y : State}
    (hx : x ∈ L.carrier)
    (hy : y ∈ L.carrier) :
    L.weylScaleReadout x = L.weylScaleReadout y := by
  rw [L.weylScale_constant hx, L.weylScale_constant hy]

end SymplecticLeaf

/-! ## 2. On-leaf modular flow -/

/-- Reversible on-leaf flow.

The field `preserves_leaf` is the only geometric law required here. Entropy and
Weyl-scale conservation are then consequences of the leaf constants. -/
structure OnLeafModularFlow
    {State : Type*}
    (L : SymplecticLeaf State) where
  /-- Time-indexed reversible flow. -/
  flow : ℝ → State → State

  /-- The flow stays on the selected leaf. -/
  preserves_leaf :
    ∀ (t : ℝ) ⦃x : State⦄, x ∈ L.carrier → flow t x ∈ L.carrier

namespace OnLeafModularFlow

variable {State : Type*}
variable {L : SymplecticLeaf State}
variable (F : OnLeafModularFlow L)

/-- Entropy is preserved by any supplied on-leaf flow. -/
theorem entropy_preserved
    (t : ℝ)
    {x : State}
    (hx : x ∈ L.carrier) :
    L.entropyReadout (F.flow t x) = L.entropyReadout x := by
  exact L.entropy_eq_of_mem (F.preserves_leaf t hx) hx

/-- Weyl scale is preserved by any supplied on-leaf flow. -/
theorem weylScale_preserved
    (t : ℝ)
    {x : State}
    (hx : x ∈ L.carrier) :
    L.weylScaleReadout (F.flow t x) = L.weylScaleReadout x := by
  exact L.weylScale_eq_of_mem (F.preserves_leaf t hx) hx

end OnLeafModularFlow

/-! ## 3. Shape readouts and transverse JKO laws -/

/-- A readout which is constant on a Souriau leaf.

This is the sidecar form of an invariant Itakura-Saito / shape-core readout.
It is deliberately weaker than a global metric theorem. -/
structure LeafInvariantReadout
    {State : Type*}
    (L : SymplecticLeaf State) where
  /-- Leaf-level shape/core readout. -/
  readout : State → ℝ

  /-- The readout is constant along the leaf. -/
  invariant_on_leaf :
    ∀ ⦃x y : State⦄,
      x ∈ L.carrier → y ∈ L.carrier →
        readout x = readout y

namespace LeafInvariantReadout

variable {State : Type*}
variable {L : SymplecticLeaf State}
variable (R : LeafInvariantReadout L)

/-- The leaf-invariant readout is preserved by any supplied on-leaf flow. -/
theorem readout_preserved_by_onLeafFlow
    (F : OnLeafModularFlow L)
    (t : ℝ)
    {x : State}
    (hx : x ∈ L.carrier) :
    R.readout (F.flow t x) = R.readout x := by
  exact R.invariant_on_leaf (F.preserves_leaf t hx) hx

end LeafInvariantReadout

/-- Witness-gated transverse JKO-style step.

The sidecar does not prescribe what the transverse law is. A concrete model may
use energy decrease, divergence decrease, entropy increase, or another
projective/Weyl criterion, but it must supply the law explicitly. -/
structure TransverseJKOFlow
    {State : Type*}
    (L : SymplecticLeaf State) where
  /-- One dissipative step. -/
  step : State → State

  /-- Model-specific transverse law. -/
  transverseLaw : State → State → Prop

  /-- The supplied step satisfies the transverse law from points on the leaf. -/
  step_law :
    ∀ ⦃x : State⦄, x ∈ L.carrier → transverseLaw x (step x)

namespace TransverseJKOFlow

variable {State : Type*}
variable {L : SymplecticLeaf State}
variable (J : TransverseJKOFlow L)

/-- Re-export the supplied transverse law for one JKO-style step. -/
theorem transverse_step
    {x : State}
    (hx : x ∈ L.carrier) :
    J.transverseLaw x (J.step x) :=
  J.step_law hx

end TransverseJKOFlow

/-! ## 4. Closure-invariant leaves -/

/-- A closure/Tomita-style involution that preserves a Souriau leaf.

This reuses the existing abstract `ClosureInvolution` and does not introduce a
new modular group. -/
structure ClosureInvariantLeaf
    {State : Type*}
    (L : SymplecticLeaf State) where
  /-- Supplied closure/Tomita/Mobius involution. -/
  closure : ClosureInvolution State

  /-- The closure sends leaf points to leaf points. -/
  closure_preserves_leaf :
    ∀ ⦃x : State⦄, x ∈ L.carrier → closure.theta x ∈ L.carrier

namespace ClosureInvariantLeaf

variable {State : Type*}
variable {L : SymplecticLeaf State}
variable (C : ClosureInvariantLeaf L)

/-- Entropy survives the supplied closure involution on the leaf. -/
theorem entropy_theta_eq
    {x : State}
    (hx : x ∈ L.carrier) :
    L.entropyReadout (C.closure.theta x) = L.entropyReadout x := by
  exact L.entropy_eq_of_mem (C.closure_preserves_leaf hx) hx

/-- Weyl scale survives the supplied closure involution on the leaf. -/
theorem weylScale_theta_eq
    {x : State}
    (hx : x ∈ L.carrier) :
    L.weylScaleReadout (C.closure.theta x) = L.weylScaleReadout x := by
  exact L.weylScale_eq_of_mem (C.closure_preserves_leaf hx) hx

end ClosureInvariantLeaf

/-! ## 6. Positive-temperature specialization alias -/

/-- Positive-Souriau-temperature leaf alias.

This exposes the projective-temperature carrier without asserting that every
positive temperature leaf is a coadjoint orbit. -/
abbrev PositiveTemperatureLeaf :=
  SymplecticLeaf PositiveSouriauTemperature

end InfoGeometry.Thermodynamics.SouriauFoliation