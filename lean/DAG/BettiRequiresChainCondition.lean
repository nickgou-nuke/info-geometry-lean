/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import DAG.SelfLoopIncidenceRegression
import Mathlib.Tactic

/-! The rank-difference diagnostic `betti1` need not be a homology dimension
without the chain condition. -/
namespace DAG.BettiRequiresChainCondition

open SelfLoopIncidenceRegression

/-- One non-loop edge with a degenerate face whose three boundary occurrences
all refer to that same edge. -/
def malformedFace : TwoComplex Nat :=
  { oneLoop with
    base := { oneLoop.base with
      toGraph := { oneLoop.base.toGraph with
        nodes := #[0, 1]
        forward := #[#[(1, EdgeKind.type)], #[]] } }
    edges := #[(0, 1)]
    faces := #[(0, 0, 0)] }

/-- The raw rank difference is `1 - 1 - 1 = -1`; a Betti number cannot have
this value. This malformed input therefore needs the chain-complex hypothesis
before `betti1` is interpreted homologically. -/
theorem rank_difference_can_be_negative :
    DAG.betti1 malformedFace = -1 := by
  native_decide

/-- The same input violates `∂₂ ∂₁ = 0`, as witnessed by the executable owner
check. -/
theorem malformed_face_fails_chain_condition :
    DAG.boundarySquaredZero malformedFace = false := by
  native_decide

end DAG.BettiRequiresChainCondition
