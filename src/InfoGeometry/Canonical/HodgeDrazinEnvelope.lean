import InfoGeometry.Canonical.DrazinGreenHorizonEnvelope
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.HodgeDrazinEnvelope

Facade for the Hodge-Drazin double filtration.

This file gives the physics-facing names for the theorem-safe carrier already
proved in `DrazinGreenHorizonEnvelope`:

* `SignalDrazinSupport` is the signal Drazin horizon `p_A = A * Aᴰ`;
* `FrequencyDrazinGreen` is the frequency/Laplacian-like Drazin-Green data;
* `HodgeDrazinCarrier` packages a raw trembling observable;
* `physicalEnvelope` is

`H_L * (p_A * x_raw * p_A) * H_L`.

The word "Hodge" is interpreted cautiously: without extra self-adjoint
Laplacian/semisimple-zero-sector hypotheses, `H_L` is the Drazin generalized
zero-sector projector, not necessarily a classical smooth harmonic projector.
-/

noncomputable section

namespace InfoGeometry.Canonical.HodgeDrazinEnvelope

open InfoGeometry.Canonical.DrazinModularPersistence

/-- Drazin data for a signal operator.  The support `p = A * AD` is the horizon. -/
abbrev SignalDrazinSupport
    (Op : Type*) [Ring Op] [Star Op] :=
  InfoGeometry.Canonical.DrazinGreenHorizonEnvelope.DrazinHorizon Op

/--
Drazin-Green data for a frequency/Laplacian-like operator.

`LD` is the algebraic Green operator, `P_reg = L * LD` is the regular sector,
and `H = 1 - P_reg` is the harmonic/generalized-zero sector.
-/
abbrev FrequencyDrazinGreen
    (Op : Type*) [Ring Op] [Star Op] :=
  InfoGeometry.Canonical.DrazinGreenHorizonEnvelope.DrazinGreenData Op

/--
Pure carrier for the Hodge-Drazin double filtration.

`signal` supplies the horizon support, `frequency` supplies the Drazin-Green
harmonic/generalized-zero projector, and `x_raw` is the trembling observable.
-/
@[rep_depth operator]
structure HodgeDrazinCarrier
    (Op : Type*) [Ring Op] [Star Op] where
  signal : SignalDrazinSupport Op
  frequency : FrequencyDrazinGreen Op
  x_raw : Op

/--
The physical matter envelope:

`x_phys = H_L * (p_A * x_raw * p_A) * H_L`.
-/
@[rep_depth operator]
def physicalEnvelope
    {Op : Type*} [Ring Op] [Star Op]
    (C : HodgeDrazinCarrier Op) : Op :=
  InfoGeometry.Canonical.DrazinGreenHorizonEnvelope.horizonHarmonicEnvelope
    C.signal C.frequency C.x_raw

/--
Combined matter support:

`e = p_A * H_L`.

This is a projection when `p_A` and `H_L` commute.
-/
@[rep_depth operator]
def matterSupport
    {Op : Type*} [Ring Op] [Star Op]
    (C : HodgeDrazinCarrier Op) : Op :=
  InfoGeometry.Canonical.DrazinGreenHorizonEnvelope.matterSupport C.signal C.frequency

/-- The physical envelope unfolds to the explicit double filtration formula. -/
@[rep_depth operator]
theorem physicalEnvelope_eq
    {Op : Type*} [Ring Op] [Star Op]
    (C : HodgeDrazinCarrier Op) :
    physicalEnvelope C =
      C.frequency.P_harm * (C.signal.p * C.x_raw * C.signal.p) * C.frequency.P_harm :=
  rfl

/--
If the signal horizon and harmonic projector commute, the combined matter
support is idempotent.
-/
@[rep_depth operator]
theorem matterSupport_idempotent
    {Op : Type*} [Ring Op] [Star Op]
    (C : HodgeDrazinCarrier Op)
    (hComm : C.signal.p * C.frequency.P_harm =
             C.frequency.P_harm * C.signal.p) :
    matterSupport C * matterSupport C = matterSupport C :=
  InfoGeometry.Canonical.DrazinGreenHorizonEnvelope.matterSupport_idempotent
    C.signal C.frequency hComm

/--
If the signal horizon and harmonic projector commute, the combined matter
support is self-adjoint.
-/
@[rep_depth operator]
theorem matterSupport_self_adjoint
    {Op : Type*} [Ring Op] [StarRing Op]
    (C : HodgeDrazinCarrier Op)
    (hComm : C.signal.p * C.frequency.P_harm =
             C.frequency.P_harm * C.signal.p) :
    star (matterSupport C) = matterSupport C :=
  InfoGeometry.Canonical.DrazinGreenHorizonEnvelope.matterSupport_self_adjoint
    C.signal C.frequency hComm

/--
When `p_A` and `H_L` commute, the two-stage envelope is compression by the
single matter support `e = p_A * H_L`.
-/
@[rep_depth operator]
theorem physicalEnvelope_eq_matterSupport_compression
    {Op : Type*} [Ring Op] [Star Op]
    (C : HodgeDrazinCarrier Op)
    (hComm : C.signal.p * C.frequency.P_harm =
             C.frequency.P_harm * C.signal.p) :
    physicalEnvelope C =
      matterSupport C * C.x_raw * matterSupport C :=
  InfoGeometry.Canonical.DrazinGreenHorizonEnvelope.envelope_eq_combined_support_compression
    C.signal C.frequency C.x_raw hComm

end InfoGeometry.Canonical.HodgeDrazinEnvelope
