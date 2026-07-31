import InfoGeometry.Canonical.DrazinHodgeResidueBridge
import InfoGeometry.Canonical.FierzReadout
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

noncomputable section

namespace InfoGeometry.Canonical

open InfoGeometry.Canonical
open InfoGeometry.Canonical.DrazinHodgeResidueBridge
open InfoGeometry.Canonical.FierzReadout

/-!
# Drazin/Hodge Fierz bridge

This module connects the calibrated Drazin/Hodge residue lane to the existing
Fierz readout owner surface.

The theorem-safe content is deliberately narrow:

* the physical envelope is the supplied harmonic projector;
* the calibrated Drazin envelope is the Drazin complementary projector;
* those envelopes are equal by the owner calibration in
  `DrazinHodgeResidueBridge`;
* Fierz channels are evaluated on the envelope, not on raw states;
* Klein/twistor/lightcone claims are represented by a supplied geometric
  predicate, not asserted as automatic consequences.
-/

section Core

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
Drazin--Hodge / Fierz bridge.

This packages the theorem-safe readback:

* the Drazin complementary projector is calibrated to a supplied harmonic
  projector;
* Fierz channels are evaluated only after applying the calibrated envelope;
* no global claim is made that arbitrary raw data automatically define a Klein
  quadric or classical spacetime.
-/
@[rep_depth operator]
structure DrazinHodgeFierzBridge where
  /-- Drazin/Hodge residue calibration. -/
  residue : DrazinHodgeResidueCalibration (E := E)

  /-- Fierz readout package on the state space used by the bridge. -/
  fierz : FierzChannelReadout

  /-- Map from the real Hilbert carrier into the Fierz state space. -/
  toFierzState : E → fierz.State

  /--
  Optional geometric readout predicate.

  Use this for Klein-quadric / Plücker / twistor claims. The bridge does not
  assert such a predicate automatically.
  -/
  geometricPredicate : fierz.State → Prop

  /--
  Witness that the harmonic/Drazin-envelope states satisfy the intended
  geometric predicate.
  -/
  geometricPredicate_on_envelope :
    ∀ x : E, geometricPredicate (toFierzState (residue.HarmonicProjector x))

namespace DrazinHodgeFierzBridge

variable (B : DrazinHodgeFierzBridge (E := E))

/-- The physical envelope is the supplied harmonic projector. -/
@[rep_depth operator]
def physicalEnvelope (x : E) : E :=
  B.residue.HarmonicProjector x

/-- The Drazin envelope is the certified Drazin complementary projector. -/
@[rep_depth operator]
def drazinEnvelope (x : E) : E :=
  B.residue.CIK.spectralComplementaryProjector x

/--
The physical envelope equals the Drazin complementary envelope by calibration.
-/
@[rep_depth operator]
theorem physicalEnvelope_eq_drazinEnvelope
    (x : E) :
    B.physicalEnvelope x = B.drazinEnvelope x := by
  unfold physicalEnvelope drazinEnvelope
  exact B.residue.harmonicProjector_apply_eq_drazinComplement_apply x

/--
Fierz scalar readout on the harmonic envelope equals Fierz scalar readout on
the Drazin envelope.
-/
@[rep_depth operator]
theorem scalar_on_physicalEnvelope_eq_scalar_on_drazinEnvelope
    (x : E) :
    B.fierz.scalar (B.toFierzState (B.physicalEnvelope x))
      =
    B.fierz.scalar (B.toFierzState (B.drazinEnvelope x)) := by
  rw [B.physicalEnvelope_eq_drazinEnvelope x]

/--
Fierz symplectic readout on the harmonic envelope equals Fierz symplectic readout
on the Drazin envelope.
-/
@[rep_depth operator]
theorem symplectic_on_physicalEnvelope_eq_symplectic_on_drazinEnvelope
    (x : E) :
    B.fierz.symplectic (B.toFierzState (B.physicalEnvelope x))
      =
    B.fierz.symplectic (B.toFierzState (B.drazinEnvelope x)) := by
  rw [B.physicalEnvelope_eq_drazinEnvelope x]

/--
Fierz Hilbert readout on the harmonic envelope equals Fierz Hilbert readout
on the Drazin envelope.
-/
@[rep_depth operator]
theorem hilbert_on_physicalEnvelope_eq_hilbert_on_drazinEnvelope
    (x : E) :
    B.fierz.hilbert (B.toFierzState (B.physicalEnvelope x))
      =
    B.fierz.hilbert (B.toFierzState (B.drazinEnvelope x)) := by
  rw [B.physicalEnvelope_eq_drazinEnvelope x]

/--
Fierz area readout on the harmonic envelope equals Fierz area readout on the
Drazin envelope.
-/
@[rep_depth operator]
theorem area_on_physicalEnvelope_eq_area_on_drazinEnvelope
    (x : E) :
    B.fierz.area (B.toFierzState (B.physicalEnvelope x))
      =
    B.fierz.area (B.toFierzState (B.drazinEnvelope x)) := by
  rw [B.physicalEnvelope_eq_drazinEnvelope x]

/--
The Fierz identity holds on the Hodge--Drazin physical envelope.
-/
@[rep_depth operator]
theorem fierzIdentity_on_physicalEnvelope
    (x : E) :
    (B.fierz.hilbert (B.toFierzState (B.physicalEnvelope x)))^2
      =
    (B.fierz.scalar (B.toFierzState (B.physicalEnvelope x)))^2
      +
    (B.fierz.symplectic (B.toFierzState (B.physicalEnvelope x)))^2
      +
    4 * (B.fierz.area (B.toFierzState (B.physicalEnvelope x))) := by
  exact B.fierz.fierzIdentity (B.toFierzState (B.physicalEnvelope x))

/--
The Fierz identity holds on the Drazin complementary envelope.
-/
@[rep_depth operator]
theorem fierzIdentity_on_drazinEnvelope
    (x : E) :
    (B.fierz.hilbert (B.toFierzState (B.drazinEnvelope x)))^2
      =
    (B.fierz.scalar (B.toFierzState (B.drazinEnvelope x)))^2
      +
    (B.fierz.symplectic (B.toFierzState (B.drazinEnvelope x)))^2
      +
    4 * (B.fierz.area (B.toFierzState (B.drazinEnvelope x))) := by
  exact B.fierz.fierzIdentity (B.toFierzState (B.drazinEnvelope x))

/--
The geometric predicate is certified on the physical envelope.

This is the theorem-safe replacement for a raw claim like
`IsOnKleinQuadric (...)`: the predicate is supplied as a witness field.
-/
@[rep_depth operator]
theorem geometricPredicate_on_physicalEnvelope
    (x : E) :
    B.geometricPredicate (B.toFierzState (B.physicalEnvelope x)) :=
  B.geometricPredicate_on_envelope x

/--
The geometric predicate is also certified on the Drazin envelope, because the
Drazin envelope equals the harmonic/physical envelope.
-/
@[rep_depth operator]
theorem geometricPredicate_on_drazinEnvelope
    (x : E) :
    B.geometricPredicate (B.toFierzState (B.drazinEnvelope x)) := by
  rw [← B.physicalEnvelope_eq_drazinEnvelope x]
  exact B.geometricPredicate_on_physicalEnvelope x

/--
If the physical envelope is a Majorana-shadow state, the Fierz identity reduces
to the two-channel identity on the envelope.
-/
@[rep_depth operator]
theorem majoranaFierz_on_physicalEnvelope
    (x : E)
    (hMajorana :
      B.fierz.IsMajoranaShadow (B.toFierzState (B.physicalEnvelope x))) :
    (B.fierz.hilbert (B.toFierzState (B.physicalEnvelope x)))^2
      =
    (B.fierz.scalar (B.toFierzState (B.physicalEnvelope x)))^2
      +
    (B.fierz.symplectic (B.toFierzState (B.physicalEnvelope x)))^2 := by
  exact FierzChannelReadout.fierz_majorana
    (R := B.fierz)
    (ψ := B.toFierzState (B.physicalEnvelope x))
    hMajorana

/--
If the Drazin envelope is a Majorana-shadow state, the Fierz identity reduces
to the two-channel identity on the Drazin envelope.
-/
@[rep_depth operator]
theorem majoranaFierz_on_drazinEnvelope
    (x : E)
    (hMajorana :
      B.fierz.IsMajoranaShadow (B.toFierzState (B.drazinEnvelope x))) :
    (B.fierz.hilbert (B.toFierzState (B.drazinEnvelope x)))^2
      =
    (B.fierz.scalar (B.toFierzState (B.drazinEnvelope x)))^2
      +
    (B.fierz.symplectic (B.toFierzState (B.drazinEnvelope x)))^2 := by
  exact FierzChannelReadout.fierz_majorana
    (R := B.fierz)
    (ψ := B.toFierzState (B.drazinEnvelope x))
    hMajorana

end DrazinHodgeFierzBridge

end Core

section DoubledSpecialization

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => InfoGeometry.Krein.DoubledSpace E

/--
Doubled-Krein specialization of the Drazin--Hodge / Fierz bridge.

A caller supplies the map from the Drazin/Hodge Hilbert carrier into the doubled
Krein Fierz carrier.
-/
@[rep_depth operator]
noncomputable def doubledDrazinHodgeFierzBridge
    (R : DrazinHodgeResidueCalibration (E := E))
    (toDoubled : E → H₂)
    (geometricPredicate : H₂ → Prop)
    (hGeo :
      ∀ x : E, geometricPredicate (toDoubled (R.HarmonicProjector x))) :
    DrazinHodgeFierzBridge (E := E) where
  residue := R
  fierz := doubledFierzReadout (E := E)
  toFierzState := toDoubled
  geometricPredicate := geometricPredicate
  geometricPredicate_on_envelope := hGeo

end DoubledSpecialization

end InfoGeometry.Canonical
