/-
InfoGeometry/OperatorAlgebra/BrewsterDrazinIntersection.lean

Brewster reflection as a Drazin rank-collapse boundary.

This module records the optical/Drazin intersection:

* Brewster condition: the p-channel reflection coefficient vanishes;
* Jones reflection collapses to a scaled s-projector;
* the reflected core is the s-sector;
* the killed/singular sector is the p-sector;
* Hessian degeneracy is connected only by an explicit calibration datum.

The Hessian singularity is not assumed to imply Brewster collapse unless a
model supplies that bridge.
-/

import Mathlib
import InfoGeometry.Optics.JonesCalibration
import InfoGeometry.OperatorAlgebra.TopologicalSnap

noncomputable section

namespace InfoGeometry.OperatorAlgebra.BrewsterDrazinIntersection

open InfoGeometry.Optics.JonesCalibration
open InfoGeometry.OperatorAlgebra.TopologicalSnap

/-! ## 1. Abstract Drazin split for a Brewster reflection -/

/--
A Drazin-style projector split for a Brewster reflection.

`R` is the reflected Jones/operator transport.

`Pcore` is the surviving reflected sector, physically the `s` sector.

`Pnil` is the killed sector, physically the `p` sector at Brewster angle.

`RD` is the inverse on the reflected core.
-/
structure BrewsterDrazinSplit
    (Op : Type*) [Ring Op] where
  /-- Reflection operator. -/
  R : Op

  /-- Surviving/core projector. -/
  Pcore : Op

  /-- Killed/singular projector. -/
  Pnil : Op

  /-- Drazin/core inverse of the reflection on the surviving sector. -/
  RD : Op

  /-- Core projector is idempotent. -/
  Pcore_idem :
    Pcore * Pcore = Pcore

  /-- Killed-sector projector is idempotent. -/
  Pnil_idem :
    Pnil * Pnil = Pnil

  /-- Complementary projectors. -/
  complementary :
    Pcore + Pnil = 1

  /-- Core and killed sectors are disjoint. -/
  disjoint_left :
    Pcore * Pnil = 0

  /-- Core and killed sectors are disjoint. -/
  disjoint_right :
    Pnil * Pcore = 0

  /-- Reflection kills the nil/p-channel sector. -/
  R_kills_nil :
    R * Pnil = 0

  /-- Reflection is supported on the core sector. -/
  R_supported_on_core :
    R * Pcore = R

  /-- Drazin/core identity. -/
  R_mul_RD_eq_core :
    R * RD = Pcore

  /-- The Drazin inverse kills the nil sector. -/
  RD_kills_nil :
    RD * Pnil = 0

namespace BrewsterDrazinSplit

variable {Op : Type*} [Ring Op]
variable (B : BrewsterDrazinSplit Op)

/--
The Brewster reflection kills the singular/p-channel sector.
-/
theorem nil_sector_killed :
    B.R * B.Pnil = 0 :=
  B.R_kills_nil

/--
The Drazin/core inverse recovers the core projector.
-/
theorem core_identity :
    B.R * B.RD = B.Pcore :=
  B.R_mul_RD_eq_core

/--
The killed sector is complementary to the core sector.
-/
theorem core_plus_nil_eq_one :
    B.Pcore + B.Pnil = 1 :=
  B.complementary

end BrewsterDrazinSplit

/-! ## 2. Brewster optical calibration -/

/--
Brewster optical calibration.

This connects a Jones event to the abstract Drazin split. The event supplies
the optical statement `r_p = 0`; the split supplies the projector algebra.
-/
structure BrewsterDrazinCalibration
    (Op : Type*) [Ring Op] where
  /-- Jones/Fresnel optical event. -/
  event : JonesOpticalEvent

  /-- The event satisfies the Brewster condition. -/
  is_brewster :
    IsBrewsterEvent event

  /-- Operator-level Drazin split for the reflected transport. -/
  split :
    BrewsterDrazinSplit Op

namespace BrewsterDrazinCalibration

variable {Op : Type*} [Ring Op]
variable (C : BrewsterDrazinCalibration Op)

/--
At Brewster calibration, the second Jones/Fresnel coefficient vanishes.
In the `s/p` basis this is `r_p = 0`.
-/
theorem rp_eq_zero :
    C.event.secondCoeff = 0 :=
  JonesOpticalEvent.brewster_secondCoeff_zero C.event C.is_brewster

/--
The surviving channel coefficient is nonzero.
In the `s/p` basis this is `r_s ≠ 0`.
-/
theorem rs_ne_zero :
    C.event.firstCoeff ≠ 0 :=
  JonesOpticalEvent.brewster_firstCoeff_ne_zero C.event C.is_brewster

/--
The operator split kills the nil/p-channel sector.
-/
theorem killed_sector :
    C.split.R * C.split.Pnil = 0 :=
  C.split.nil_sector_killed

/--
The reflected core identity.
-/
theorem reflected_core_identity :
    C.split.R * C.split.RD = C.split.Pcore :=
  C.split.core_identity

end BrewsterDrazinCalibration

/-! ## 3. Hessian degeneracy bridge -/

/--
Bregman/Hessian degeneracy datum.

This is intentionally abstract. In a concrete optical material model, the
Hessian may be the response/susceptibility metric induced by a Bregman or
Legendre potential.
-/
structure HessianDegeneracyDatum
    (State : Type*) where
  /-- Degeneracy predicate for the thermodynamic/information Hessian. -/
  IsDegenerate : State → Prop

  /-- Singular direction/readout, for example the p-sector. -/
  singularDirection : State → Prop

/--
Bridge saying that Hessian degeneracy is calibrated to Brewster collapse.

This is the safe replacement for the overstrong theorem
“Hessian singularity automatically forces `r_p = 0`.”
-/
structure BrewsterHessianBridge
    (Op State : Type*) [Ring Op]
    (C : BrewsterDrazinCalibration Op)
    (H : HessianDegeneracyDatum State) where
  /-- State associated to the optical event. -/
  stateOfEvent : State

  /--
  Hessian degeneracy implies the Brewster event.

  In concrete optics, this says the response-metric singular locus coincides
  with the Fresnel p-channel zero.
  -/
  hessian_degenerate_implies_brewster :
    H.IsDegenerate stateOfEvent →
      IsBrewsterEvent C.event

  /--
  Brewster event implies Hessian degeneracy.

  Optional but useful for exact identification of the two loci.
  -/
  brewster_implies_hessian_degenerate :
    IsBrewsterEvent C.event →
      H.IsDegenerate stateOfEvent

namespace BrewsterHessianBridge

variable {Op State : Type*} [Ring Op]
variable {C : BrewsterDrazinCalibration Op}
variable {H : HessianDegeneracyDatum State}
variable (B : BrewsterHessianBridge Op State C H)

/--
If the calibrated Hessian degenerates, then the p-channel coefficient vanishes.
-/
theorem rp_zero_of_hessian_degenerate
    (h : H.IsDegenerate B.stateOfEvent) :
    C.event.secondCoeff = 0 := by
  have hBrewster : IsBrewsterEvent C.event :=
    B.hessian_degenerate_implies_brewster h
  exact JonesOpticalEvent.brewster_secondCoeff_zero C.event hBrewster

/--
Under the bridge, Brewster collapse and Hessian degeneracy are equivalent.
-/
theorem hessian_degenerate_iff_brewster :
    H.IsDegenerate B.stateOfEvent ↔ IsBrewsterEvent C.event := by
  constructor
  · exact B.hessian_degenerate_implies_brewster
  · exact B.brewster_implies_hessian_degenerate

end BrewsterHessianBridge

/-! ## 4. Topological snap interface -/

/--
A Brewster-Drazin event can be treated as a topological snap boundary when it
carries a conserved obstruction charge.
-/
structure BrewsterSnapBoundary
    (Op State Charge : Type*) [Ring Op] [Zero Charge] where
  calibration :
    BrewsterDrazinCalibration Op

  obstruction :
    State → Charge

  flatSector :
    Set State

  flow :
    ℝ → State → State

  flat_obstruction_zero :
    ∀ x : State, x ∈ flatSector → obstruction x = 0

  obstruction_conserved :
    ∀ t x, obstruction (flow t x) = obstruction x

/--
Convert a Brewster snap boundary into a conserved-obstruction flow.
-/
def BrewsterSnapBoundary.toConservedObstructionFlow
    {Op State Charge : Type*} [Ring Op] [Zero Charge]
    (B : BrewsterSnapBoundary Op State Charge) :
    ConservedObstructionFlow State Charge where
  invariant := B.obstruction
  Flat := B.flatSector
  flow := B.flow
  flat_invariant_zero := B.flat_obstruction_zero
  flow_preserves_invariant := B.obstruction_conserved

namespace BrewsterSnapBoundary

variable {Op State Charge : Type*} [Ring Op] [Zero Charge]
variable (B : BrewsterSnapBoundary Op State Charge)

/--
A nontrivial Brewster obstruction cannot relax into the flat optical sector.
-/
theorem nontrivial_cannot_flow_to_flat
    {x : State}
    (hx : B.obstruction x ≠ 0)
    (t : ℝ) :
    B.flow t x ∉ B.flatSector :=
  (B.toConservedObstructionFlow).nontrivial_cannot_flow_to_flat hx t

end BrewsterSnapBoundary

end InfoGeometry.OperatorAlgebra.BrewsterDrazinIntersection
