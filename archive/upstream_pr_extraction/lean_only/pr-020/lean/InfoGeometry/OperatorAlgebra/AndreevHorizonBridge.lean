/-
InfoGeometry/OperatorAlgebra/AndreevHorizonBridge.lean

Optional Andreev/horizon analogue bridge.

This module does not assert that a black-hole horizon is literally a
superconducting surface. It records an optional witness saying that a concrete
model treats a horizon boundary as an Andreev-like closure mirror, then exports
only the algebraic Andreev consequences.
-/

import Mathlib
import InfoGeometry.OperatorAlgebra.AndreevBoundary

noncomputable section

namespace InfoGeometry.OperatorAlgebra.AndreevHorizonBridge

open InfoGeometry.OperatorAlgebra.AndreevBoundary
open InfoGeometry.OperatorAlgebra.ClosureInvolution

set_option linter.dupNamespace false

/--
Witness-gated bridge between horizon data and an Andreev boundary.

`horizon_as_andreev_boundary_law` is the installed analogue/holographic model
law. Without it, this structure makes no claim that horizons are
superconducting interfaces.
-/
structure AndreevHorizonBridge
    (V HorizonData : Type*)
    [AddCommGroup V] [Module ℝ V] where
  andreev :
    AndreevBoundaryDatum V

  horizonData :
    HorizonData

  /-- Model-specific law identifying the horizon boundary with the Andreev closure. -/
  horizon_as_andreev_boundary_law :
    Prop

  /-- Proof/certificate of the analogue horizon/Andreev law. -/
  horizon_as_andreev_boundary_certificate :
    horizon_as_andreev_boundary_law

namespace AndreevHorizonBridge

variable
    {V HorizonData : Type*}
    [AddCommGroup V] [Module ℝ V]

variable (B : AndreevHorizonBridge V HorizonData)

/-- The supplied horizon-as-Andreev analogue law is available. -/
theorem horizon_as_andreev_boundary_valid :
    B.horizon_as_andreev_boundary_law :=
  B.horizon_as_andreev_boundary_certificate

/-- The bridge exports the Andreev diagonal fixedness theorem. -/
theorem horizon_diagonal_fixed :
    B.andreev.electron + B.andreev.hole ∈
      B.andreev.closure.Fixed :=
  B.andreev.electron_hole_diagonal_fixed

/-- The bridge exports the Andreev diagonal transparency theorem. -/
theorem horizon_diagonal_transparent :
    B.andreev.closure.theta (B.andreev.electron + B.andreev.hole) =
      B.andreev.electron + B.andreev.hole :=
  B.andreev.electron_hole_diagonal_transparent

/-- The bridge exports the Andreev imbalance anti-fixedness theorem. -/
theorem horizon_imbalance_anti_fixed :
    B.andreev.closure.theta (B.andreev.electron - B.andreev.hole) =
      -(B.andreev.electron - B.andreev.hole) :=
  B.andreev.electron_hole_imbalance_anti_fixed

end AndreevHorizonBridge

end InfoGeometry.OperatorAlgebra.AndreevHorizonBridge
