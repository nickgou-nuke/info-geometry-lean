import InfoGeometry.Physics.WeightGrading55
import InfoGeometry.Algebra.Cl11Fermions
import Mathlib.Tactic

/-!
## Mathematical content

This file now records only the finite local compensation data currently proved in
repo:

* the Cl(1,1) pair `b`, `bdag` is nilpotent on both sides;
* the anticommutator relation `b * bdag + bdag * b = 1` holds exactly;
* every `JordanMatrix10D` has a refined orbit tag from `WeightGrading55`.

Boundary: this file does not prove a genuine Witten index theorem, a supertrace
computation, or a global anomaly-cancellation statement. Those remain separate
closure debt until explicit graded trace data and Möbius recursion are added.
-/

open InfoGeometry.Physics.WeightGrading55.JordanMatrix10D
open Cl11Fermions

namespace InfoGeometry.Physics.OrbitIndexClosure

/-! ## 1. Local Cl(1,1) compensation identities -/

/-- The concrete local Cl(1,1) compensation packet is honest finite data. -/
theorem cl11_local_compensation_identities :
    b * b = 0 ∧ bdag * bdag = 0 ∧ (b * bdag + bdag * b = 1) := by
  refine ⟨?_, ?_, ?_⟩
  · exact b_sq
  · exact bdag_sq
  · exact anticomm_bbdag

/-! ## 2. Refined orbit tags available from the 5-graded model -/

/--
At the current finite level, every `JordanMatrix10D` carries a refined orbit tag
from `WeightGrading55`.
-/
theorem refined_orbit_tag_exists
    (X : InfoGeometry.Physics.OrbitClassification55.JordanMatrix10D) :
    RefinedOrbitType X := by
  exact refined_orbit_classification X

/-! ## 3. Boundary for future global compensation theorems -/

/--
Current boundary theorem: the local Cl(1,1) compensation relation is available
as exact algebraic data, but no global charge or index functional is defined in
this file yet.
-/
theorem local_compensation_anticommutator :
    b * bdag + bdag * b = 1 :=
  anticomm_bbdag

end InfoGeometry.Physics.OrbitIndexClosure
