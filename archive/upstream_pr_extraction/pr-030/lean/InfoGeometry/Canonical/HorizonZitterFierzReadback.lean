import InfoGeometry.Canonical.HorizonZitterFierzReadout
import InfoGeometry.Meta.Architecture

/-!
# Horizon zitter Fierz readback

Canonical readback-facing facade for horizon zitter Fierz coordinates.

`HorizonZitterModes` owns the real operator-theoretic core:

* Drazin horizon support;
* modular fixedness;
* chiral/CPT/V₄-style trembling;
* frequency-side harmonic projection;
* harmonic zero-mode envelope.

`HorizonZitterFierzReadout` owns the existing expectation/channel coordinate
definitions and compatibility-assumption readbacks.

This file gives the doctrine the requested module name without renaming the
existing module or changing its API.  The residual theorem remains explicitly
assumption-derived.
-/

noncomputable section

namespace InfoGeometry.Canonical.HorizonZitterFierzReadback

open InfoGeometry.Canonical.DrazinModularPersistence
open InfoGeometry.Canonical.HorizonZitterModes

/-!
The following aliases intentionally preserve the original implementation
surface while exposing the readback terminology.
-/

/-- Readback name for the horizon-zitter Fierz coordinate vector. -/
@[rep_depth operator]
def horizonZitterFierzReadbackVector
    {Obs : Type*}
    [Ring Obs] [Star Obs]
    (φA : RealExpectationState Obs)
    (C : FierzChannelMap Obs)
    (Z : HorizonZitterMode Obs) :
    FierzCoordinates :=
  InfoGeometry.Canonical.HorizonZitterFierzReadout.horizonZitterFierzVector φA C Z

/-- Readback name for the horizon-zitter Fierz compatibility assumption packet. -/
@[rep_depth operator]
abbrev HorizonZitterFierzReadbackAssumption :=
  InfoGeometry.Canonical.HorizonZitterFierzReadout.HorizonZitterFierzCompatibilityAssumption

/--
Assumption-derived Fierz readback for horizon zitter envelopes.

This theorem is a readback from an explicit compatibility-assumption packet,
not an owner-derived proof that modular fixedness alone implies a Fierz
quadric.
-/
@[rep_depth operator]
theorem horizonZitter_fierz_readback_from_assumption
    {Obs : Type*}
    [Ring Obs] [Star Obs]
    (K : HorizonZitterFierzReadbackAssumption Obs)
    (Z : HorizonZitterMode Obs) :
    K.residual.residual
      (horizonZitterFierzReadbackVector K.state K.channels Z) = 0 :=
  InfoGeometry.Canonical.HorizonZitterFierzReadout.horizonZitter_fierz_quadric_from_assumption K Z

end InfoGeometry.Canonical.HorizonZitterFierzReadback
