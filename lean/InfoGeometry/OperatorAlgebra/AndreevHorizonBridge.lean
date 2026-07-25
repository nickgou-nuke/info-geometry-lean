/-
InfoGeometry/OperatorAlgebra/AndreevHorizonBridge.lean

Optional Andreev/horizon analogue carrier.

This module does not assert that a black-hole horizon is literally a
superconducting surface. It records a concrete Andreev boundary datum together
with opaque horizon data, then exports only the algebraic Andreev consequences.
-/

import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.AndreevBoundary

noncomputable section

namespace InfoGeometry.OperatorAlgebra.AndreevHorizonBridge

open InfoGeometry.OperatorAlgebra.AndreevBoundary
open InfoGeometry.OperatorAlgebra.ClosureInvolution

set_option linter.dupNamespace false

/-- Carrier pairing horizon data with an installed Andreev boundary datum. -/
structure AndreevHorizonBridge
    (V HorizonData : Type*)
    [AddCommGroup V] [Module ℝ V] where
  andreev :
    AndreevBoundaryDatum V

  horizonData :
    HorizonData

namespace AndreevHorizonBridge

variable
    {V HorizonData : Type*}
    [AddCommGroup V] [Module ℝ V]

variable (B : AndreevHorizonBridge V HorizonData)

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
