import InfoGeometry.Canonical.FierzKleinFoundation
import InfoGeometry.Meta.Architecture

/-!
# Operator Erlangen Fierz--Klein lift

The Fierz--Klein quadric is treated here as an Erlangen-style invariant of a
Drazin-stabilized modular horizon.

This module is a theorem-safe facade over existing owners:

* `DrazinModularPersistence` owns Drazin supports, modular zero modes, physical
  horizons, and no-leakage;
* `FierzKleinFoundation` owns the real-coordinate Fierz--Klein bridge.

The operator layer introduced here does not claim that arbitrary Type III
observables satisfy Fierz identities.  It records:

* a Drazin support horizon;
* modular fixedness of that horizon;
* operator-valued Fierz channel maps;
* explicit zero-mode certificates for those channel observables;
* an explicit Fierz-admissibility property.

With those witnesses, the Fierz--Klein conclusion is derived from the existing
foundation theorem.
-/

noncomputable section

namespace InfoGeometry.Canonical.OperatorErlangenFierzKlein

universe u

set_option linter.dupNamespace false

open InfoGeometry.Canonical.DrazinModularPersistence
open InfoGeometry.Canonical.FierzKleinFoundation
open InfoGeometry.OperatorAlgebra.Thermodynamics

/-! ## 1. Operator-valued Fierz channels -/

/--
Operator-valued Fierz channel maps.

These are the pre-readout channels `C_α`.  Numeric Fierz coordinates are
obtained only after applying a real expectation state to these observables.
-/
@[rep_depth operator]
structure OperatorFierzChannelMaps
    (Obs : Type*) where
  scalar : Obs → Obs
  phase : Obs → Obs
  vector : I4 → Obs → Obs
  axial : I4 → Obs → Obs
  area : Obs → Bivector4

/--
Expectation readout of operator-valued Fierz channels.

The area channel is already a bivector readout; scalar, phase, vector, and
axial channels are measured by the supplied real expectation state.
-/
@[rep_depth operator]
def expectationFierzReadout
    {Obs : Type*}
    [Ring Obs] [Star Obs]
    (φA : RealExpectationState Obs)
    (C : OperatorFierzChannelMaps Obs)
    (D : DrazinSupportData Obs) :
    FierzReadoutChannels Obs where
  scalar x := φA.expect (C.scalar x)
  phase x := φA.expect (C.phase x)
  vector μ x := φA.expect (C.vector μ x)
  axial μ x := φA.expect (C.axial μ x)
  area := C.area D.AD

/--
The operator Fierz channels are horizon zero modes when their observables,
evaluated at `Aᴰ`, are fixed by the modular flow.

The bivector area readout is numeric in this abstraction, so no separate
operator zero-mode condition is imposed on `area`.
-/
@[rep_depth operator]
def OperatorFierzChannelsAreHorizonZeroModes
    {Obs : Type*}
    [Ring Obs] [Star Obs]
    (flow : ModularFlow Obs)
    (D : DrazinSupportData Obs)
    (C : OperatorFierzChannelMaps Obs) : Prop :=
  IsModularZeroMode flow (C.scalar D.AD) ∧
  IsModularZeroMode flow (C.phase D.AD) ∧
  (∀ μ : I4, IsModularZeroMode flow (C.vector μ D.AD)) ∧
  (∀ μ : I4, IsModularZeroMode flow (C.axial μ D.AD))

/-! ## 2. Operator Erlangen data -/

/--
Operator Erlangen Fierz--Klein data.

This structure represents the Type III operator lift of the classical
Fierz--Klein bridge:

`Drazin horizon -> modular zero modes -> expectation-valued Fierz coordinates
 -> Klein/Pluecker geometry`.

The Fierz identities are supplied as `fierz_admissible`; they are not inferred
from modular fixedness alone.
-/
@[rep_depth operator]
structure OperatorErlangenFierzKlein
    (Obs : Type*)
    [Ring Obs] [Star Obs] where
  state :
    RealExpectationState Obs
  flow :
    ModularFlow Obs
  horizon :
    DrazinSupportData Obs
  physical_horizon :
    IsPhysicalHorizon flow horizon
  channels :
    OperatorFierzChannelMaps Obs
  channel_zero_modes :
    OperatorFierzChannelsAreHorizonZeroModes flow horizon channels
  fierz_admissible :
    HorizonFierzAdmissible
      (expectationFierzReadout state channels horizon)
      horizon

namespace OperatorErlangenFierzKlein

variable {Obs : Type*}
variable [Ring Obs] [Star Obs]
variable (E : OperatorErlangenFierzKlein Obs)

/-- The real Fierz readout channels obtained from expectation values. -/
@[rep_depth operator]
def readoutChannels : FierzReadoutChannels Obs :=
  expectationFierzReadout E.state E.channels E.horizon

/-- The expectation-valued Fierz bilinear package of the operator horizon. -/
@[rep_depth operator]
def fierzBilinears : FierzBilinears :=
  horizonFierzBilinears E.readoutChannels E.horizon

/-- The Fierz--Klein coordinates associated to the operator horizon. -/
@[rep_depth operator]
def coordinates : FierzKleinCoordinates :=
  fierzKleinCoordinates E.fierzBilinears E.fierz_admissible.normalization

/-- The chiral Pluecker/Klein lift of the operator Fierz package. -/
@[rep_depth operator]
def kleinLift : Bivector4 :=
  chiralPlucker E.fierzBilinears

/-- Readback: the Drazin horizon is modular-fixed. -/
@[rep_depth operator]
theorem horizon_is_physical :
    IsPhysicalHorizon E.flow E.horizon :=
  E.physical_horizon

/-- Readback: the operator Fierz channel observables are modular zero modes. -/
@[rep_depth operator]
theorem channels_are_zero_modes :
    OperatorFierzChannelsAreHorizonZeroModes E.flow E.horizon E.channels :=
  E.channel_zero_modes

/-- Readback: the expectation Fierz package satisfies the supplied FPK identities. -/
@[rep_depth operator]
theorem fpk_identities :
    FPKIdentities E.fierzBilinears :=
  E.fierz_admissible.fpk

/-- The right chiral ray of the operator Fierz package is null. -/
@[rep_depth operator]
theorem right_chiral_ray_null :
    minkowskiDot (rightChiralRay E.fierzBilinears) (rightChiralRay E.fierzBilinears) = 0 :=
  rightChiralRay_null E.fierzBilinears E.fierz_admissible.fpk

/-- The left chiral ray of the operator Fierz package is null. -/
@[rep_depth operator]
theorem left_chiral_ray_null :
    minkowskiDot (leftChiralRay E.fierzBilinears) (leftChiralRay E.fierzBilinears) = 0 :=
  leftChiralRay_null E.fierzBilinears E.fierz_admissible.fpk

/-- The Klein/Pluecker lift of the operator Fierz package lies on the Klein quadric. -/
@[rep_depth operator]
theorem klein_lift_on_quadric :
    IsOnKleinQuadric E.kleinLift :=
  chiralPlucker_on_klein E.fierzBilinears

/-- The normalized scalar-phase coordinates lie on the scalar Fierz quadric. -/
@[rep_depth operator]
theorem scalar_phase_on_quadric :
    IsOnScalarPhaseFierzQuadric E.coordinates.scalarPhase :=
  normalizedScalarPhase_on_quadric
    E.fierzBilinears
    E.fierz_admissible.normalization

/--
Operator Erlangen Fierz--Klein invariant.

Given a physical Drazin horizon, modular-zero Fierz channel observables, and
explicit Fierz admissibility, the expectation-valued coordinates lie on
`S¹_Fierz × Q_Klein`.
-/
@[rep_depth operator]
theorem operator_erlangen_fierz_klein_holds :
    IsOnFierzKleinVariety E.coordinates :=
  horizon_fierz_klein_holds
    E.readoutChannels
    E.horizon
    E.fierz_admissible

end OperatorErlangenFierzKlein

/-! ## 3. Owner target -/

/-- Parameterized owner target for the operator Erlangen Fierz--Klein data. -/
@[rep_depth operator]
def OperatorErlangenFierzKleinTarget
    (Obs : Type u)
    [Ring Obs] [Star Obs] : Type u :=
  OperatorErlangenFierzKlein Obs

/-- Constructor for the operator Erlangen Fierz--Klein target. -/
@[rep_depth operator]
def constructOperatorErlangenFierzKleinTarget
    {Obs : Type u}
    [Ring Obs] [Star Obs]
    (E : OperatorErlangenFierzKlein Obs) :
    OperatorErlangenFierzKleinTarget Obs :=
  E

/-- The constructed target preserves the Fierz--Klein variety readout. -/
@[rep_depth operator]
theorem constructOperatorErlangenFierzKleinTarget_holds
    {Obs : Type u}
    [Ring Obs] [Star Obs]
    (E : OperatorErlangenFierzKlein Obs) :
    IsOnFierzKleinVariety
      (constructOperatorErlangenFierzKleinTarget E).coordinates :=
  (constructOperatorErlangenFierzKleinTarget E).operator_erlangen_fierz_klein_holds

end InfoGeometry.Canonical.OperatorErlangenFierzKlein
