import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Module.Basic
import InfoGeometry.Canonical.SouriauCasimirInvariant

/-!
# InfoGeometry.Canonical.SouriauOrbitDynamics

Trajectory-level orbit dynamics boundary for the Souriau affine-coadjoint lane.

This file is intentionally abstract. It does not construct concrete flows for
`G₂(2)`, `G₂*`, or `Spin(5,5)`. It only packages the theorem-facing interface
needed for statements of the form `dS/dt = 0` along symmetry trajectories.

Repository policy boundary:
this file does not replace the invariant-theory owner surface in
`SouriauCasimirInvariant`. It provides the dynamics-side carrier for later
derivative/entropy-production theorems once a concrete notion of derivative is
instantiated.
-/

noncomputable section

namespace InfoGeometry.Canonical.SouriauOrbitDynamics

universe u

/--
Abstract trajectory data over a time index.

`velocity` is a supplied first-variation property; no analytic construction is
claimed in this file.
-/
structure TrajectoryData (Time State Vel : Type u) where
  curve : Time → State
  velocity : Time → Vel

/--
Abstract derivative readout for scalar observables along trajectories.

This is a bridge interface from geometric dynamics to scalar entropy
production statements.
-/
structure DerivativeAlong
    (Time State Vel Scalar : Type u) where
  deriv :
    (State → Scalar) →
    TrajectoryData Time State Vel →
    Time → Scalar

/--
Entropy nondissipation along a trajectory: abstract `dS/dt = 0`.
-/
def EntropyNondissipative
    {Time State Vel Scalar : Type u}
    [Zero Scalar]
    (D : DerivativeAlong Time State Vel Scalar)
    (S : State → Scalar)
    (γ : TrajectoryData Time State Vel) : Prop :=
  ∀ t, D.deriv S γ t = 0

/--
Dynamics owner theorem surface.

This packages the expected trajectory-level closure as theorem-carrying data,
without asserting a concrete differentiability model.
-/
structure OrbitDynamicsDatum
    (Time State Vel Scalar : Type u) [Zero Scalar] where
  deriv : DerivativeAlong Time State Vel Scalar
  entropy : State → Scalar
  trajectory : TrajectoryData Time State Vel
  entropy_nondissipative :
    EntropyNondissipative deriv entropy trajectory

namespace OrbitDynamicsDatum

variable {Time State Vel Scalar : Type u}
variable [Zero Scalar]

/-- Readout: `dS/dt = 0` along the supplied trajectory. -/
theorem entropy_derivative_eq_zero
    (D : OrbitDynamicsDatum Time State Vel Scalar)
    (t : Time) :
    D.deriv.deriv D.entropy D.trajectory t = 0 :=
  D.entropy_nondissipative t

end OrbitDynamicsDatum

end InfoGeometry.Canonical.SouriauOrbitDynamics
