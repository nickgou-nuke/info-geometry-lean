/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.MatrixStagePartialTrace

/-!
# Scratch candidate: extend one finite matrix density to the dyadic tower

This is a construction note in Lean syntax, not a certified owner.  The chosen
finite density is kept as a full matrix.  Below its stage it is restricted by
the normalized partial trace; above its stage it is extended by the existing
unital matrix-stage embedding (a tracial tail).

The required family law is the backward condition
`D n = normalizedPartialTraceStep n (D (n+1))`.  The old forward density law
`D (n+1) = concreteStep n (D n)` is deliberately not used: that stronger law
would force the chosen density itself to have a tracial tail.

No `sorry` is used here.  The unresolved dependent-index transport and
adjacent-stage compatibility obligations are listed as propositions at the
end, rather than asserted as proved theorems.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.MatrixStagePartialTraceExtensionDraft

open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.Canonical.CuntzMatrixTraceTower
open InfoGeometry.Canonical.CuntzMatrixCompatibleStateNet
open InfoGeometry.QuantumContext.MatrixStagePartialTrace

/-- Iterated normalized partial trace over the final `r` tensor factors. -/
def partialTraceIter (n : ℕ) : (r : ℕ) → MatrixStage (n + r) → MatrixStage n
  | 0, D => D
  | r + 1, D => partialTraceIter n r (normalizedPartialTraceStep (n + r) D)

/-- The lower-stage density obtained by iterating partial trace from stage `k`.
The cast identifies `n + (k - n)` with `k` under the supplied inequality. -/
def restrictDensityTo (n k : ℕ) (hnk : n ≤ k) (Dk : MatrixStage k) :
    MatrixStage n :=
  partialTraceIter n (k - n)
    (by
      exact cast (congrArg MatrixStage (by omega)).symm Dk)

/-- Candidate density family extending `Dk`.  For stages below `k`, use
partial trace; for stages at or above `k`, use the canonical matrix embedding. -/
def extendDensity (k : ℕ) (Dk : MatrixStage k) :
    ∀ n : ℕ, MatrixStage n := fun n =>
  if h : n ≤ k then
    restrictDensityTo n k h Dk
  else
    rawMap (Nat.le_of_not_ge h) Dk

/-- The extension agrees with the originally selected density at its stage. -/
theorem extendDensity_at_selected_stage (k : ℕ) (Dk : MatrixStage k) :
    extendDensity k Dk k = Dk := by
  simp [extendDensity, restrictDensityTo, partialTraceIter]

/-!
### Remaining proof obligations for the candidate

These are named Prop readouts to keep the scratch file honest without inserting
unfinished declarations into a Lean owner.  The first two expose the exact
transport obligations for proving `PartialTraceCompatible (extendDensity k
Dk)`.  They are the only nontrivial cases after unfolding `extendDensity`:

* below `k`, iterated partial trace must commute with one more partial-trace
  step after the `n + (k - n)` casts are normalized;
* at/above `k`, normalized partial trace must commute with the transitive
  `rawMap`, reducing to `normalizedPartialTraceStep_concreteStep` and the
  `rawMap` successor law.

Once those are proved, the already-owned theorem
`weightedStageFunctional_compatible_of_partialTraceCompatible` gives the
compatible functional, and `partialTraceCompatibleColimitFunctional` gives
its quotient-colimit descent.
-/

def belowSelectedStageCompatibilityGoal : Prop :=
  ∀ (n k : ℕ) (hn : n < k) (Dk : MatrixStage k),
    restrictDensityTo n k (Nat.le_of_lt hn) Dk =
      normalizedPartialTraceStep n
        (restrictDensityTo (n + 1) k (by omega) Dk)

def aboveSelectedStageCompatibilityGoal : Prop :=
  ∀ (k n : ℕ) (hn : k < n) (Dk : MatrixStage k),
    rawMap (Nat.le_of_lt hn) Dk =
      normalizedPartialTraceStep n
        (rawMap (Nat.le_of_lt (Nat.lt_trans hn (Nat.lt_succ_self n))) Dk)

end InfoGeometry.QuantumContext.MatrixStagePartialTraceExtensionDraft

end
