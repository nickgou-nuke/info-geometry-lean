import InfoGeometry.Canonical.NoetherInference
import InfoGeometry.Canonical.RelationalInformationDynamics
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.NoetherRelationalBridge

Minimal bridge between the Noether Fisher/Hessian bilinear readout and the
relational dynamics channel metric.

This file only records the source-owned identification that both surfaces
evaluate the same doubled-state Hessian form. It does not assert a scalar
log-readout second-variation theorem.
-/

namespace NoetherRelationalBridge

open InfoGeometry.Krein
open InfoGeometry.Canonical.NoetherInference
open InfoGeometry.Canonical.RelationalInformationDynamics

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [FiniteDimensional ℝ E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/--
Source-faithful Fisher/channel bridge.

`fisherBilinAt` is the same state-evaluated Hessian bilinear form as the
relational dynamics `channelKreinMetricAtState`. This identifies the Fisher layer
with the already-owned channel readout; it does not assert a scalar log-readout
second-variation theorem.
-/
@[rep_depth krein]
theorem fisherBilinAt_eq_channelKreinMetricAtState
    (v : H₂) (X Y : EndH) :
    fisherBilinAt (E := E) v X Y
      =
    channelKreinMetricAtState (E := E) v X Y := by
  rw [fisherBilinAt_apply, channelKreinMetricAtState_apply]

end Core

end NoetherRelationalBridge
