import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Real.Basic
import InfoGeometry.Canonical.KleinExceptionalBraid

namespace InfoGeometry.Canonical.KleinBerryPhase

open Matrix
open InfoGeometry.Canonical.KleinExceptionalBraid

/-!
# Local Berry Phase Invariants around Non-Orientable Exceptional Points

Formalizes the exact cancellation of the topological Berry phase on a Klein manifold.
Based on the unoriented cobordism constraint, two consecutive encirclements
across the non-orientable bottleneck yield a trivial holonomy `+I`,
whereas a purely orientable cycle yields a geometric phase of `-I` (π).
-/

/-- 
Theorem: Orientable Holonomy. 
Two standard encirclements of the EP accumulate a Berry phase of π (represented by -I).
-/
theorem orientable_holonomy_pi :
    B_EP * B_EP = -1 := by
  decide

/-- 
Theorem: Klein Twist Holonomy. 
Two encirclements of the EP, one standard and one across the non-orientable glide twist,
accumulate a trivial Berry phase of 0 (represented by +I).
Because the glide twist anti-isomorphism forces `Twisted B = -B`, the product is `B * -B = I`.
-/
theorem klein_holonomy_cancellation :
    B_EP * (G_Glide * B_EP * G_Glide) = 1 := by
  decide

end InfoGeometry.Canonical.KleinBerryPhase
