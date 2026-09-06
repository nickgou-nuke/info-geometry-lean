import InfoGeometry.Canonical.HorizonZitterModes
import InfoGeometry.Meta.Architecture

/-!
# Horizon zitter Fierz readout

Optional Fierz/channel readout layer for horizon zitter modes.

The core `HorizonZitterModes` module is the real operator-algebraic socket:
modular flow, Drazin horizon, chiral/CPT involution, frequency Drazin
projector, harmonic envelope, and zero-mode predicates.

This file adds readout coordinates and residual laws.  The Fierz residual
vanishing theorem is explicitly assumption-derived: the conclusion is read from
an assumption packet, not derived from horizon localization or modular fixedness
alone.
-/

noncomputable section

namespace InfoGeometry.Canonical.HorizonZitterFierzReadout

open InfoGeometry.Canonical.DrazinModularPersistence
open InfoGeometry.Canonical.HorizonZitterModes

/--
Fierz vector of a horizon zitter mode.

The readout is taken on the harmonic envelope, not on the raw trembling
observable.
-/
@[rep_depth operator]
def horizonZitterFierzVector
    {Obs : Type*}
    [Ring Obs] [Star Obs]
    (φA : RealExpectationState Obs)
    (C : FierzChannelMap Obs)
    (Z : HorizonZitterMode Obs) :
    FierzCoordinates :=
  fun ch => φA.expect (C.channel ch Z.envelope)

/--
Compatibility assumption for horizon zitter Fierz geometry.

This is not an owner-derived theorem.  Horizon localization and modular
zero-mode status alone do not imply the residual law.
-/
@[rep_depth operator]
structure HorizonZitterFierzCompatibilityAssumption
    (Obs : Type*)
    [Ring Obs] [Star Obs] where
  state : RealExpectationState Obs
  channels : FierzChannelMap Obs
  residual : FierzResidual
  compatibility_assumption :
    ∀ Z : HorizonZitterMode Obs,
      residual.residual (horizonZitterFierzVector state channels Z) = 0

/--
Assumption-derived Fierz readback for horizon zitter envelopes.
-/
@[rep_depth operator]
theorem horizonZitter_fierz_quadric_from_assumption
    {Obs : Type*}
    [Ring Obs] [Star Obs]
    (K : HorizonZitterFierzCompatibilityAssumption Obs)
    (Z : HorizonZitterMode Obs) :
    K.residual.residual (horizonZitterFierzVector K.state K.channels Z) = 0 :=
  K.compatibility_assumption Z

end InfoGeometry.Canonical.HorizonZitterFierzReadout
