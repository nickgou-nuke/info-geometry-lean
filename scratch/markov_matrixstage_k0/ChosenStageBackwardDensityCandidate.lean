/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.MatrixStagePartialTrace

/-!
# Exploratory chosen-stage extension of a full matrix density

This scratch candidate addresses one precise gap: given a full matrix `Dk` at
stage `k`, construct a family at every dyadic stage satisfying the backward
normalized-partial-trace law.  Below `k` the candidate iterates normalized
partial trace; above `k` it uses the existing noncommutative tower embedding.

The declarations below do not claim positivity or state normalization of the
chosen matrix.  The only claimed target is the exact family equation
`PartialTraceCompatible`.  This file is an uncompiled proof candidate; the
cast/iteration compatibility obligation at lower stages remains explicit.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.ChosenStageBackwardDensityCandidate

open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.Canonical.CuntzMatrixTraceTower
open InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit
open InfoGeometry.QuantumContext.MatrixStagePartialTrace

/-- Trace away the last `r` dyadic factors, one normalized factor at a time. -/
def partialTraceIter (n : ℕ) : (r : ℕ) → MatrixStage (n + r) → MatrixStage n
  | 0, D => D
  | r + 1, D => partialTraceIter n r
      (normalizedPartialTraceStep (n + r) D)

/-- Restriction of a stage-`k` matrix to stage `n`, for `n ≤ k`. -/
def restrictDensityTo (n k : ℕ) (hnk : n ≤ k) (Dk : MatrixStage k) :
    MatrixStage n :=
  partialTraceIter n (k - n)
    (cast (congrArg MatrixStage (by omega : n + (k - n) = k)).symm Dk)

/-- Extend a chosen stage matrix to the whole tower.  The upper tail is the
existing raw matrix embedding, so no scalar or diagonal carrier is introduced. -/
def extendDensity (k : ℕ) (Dk : MatrixStage k) : ∀ n : ℕ, MatrixStage n :=
  fun n => if h : n ≤ k then restrictDensityTo n k h Dk
    else rawMap (Nat.le_of_not_ge h) Dk

/-- At the chosen stage the restriction has length zero and returns `Dk`. -/
theorem extendDensity_at_selected_stage (k : ℕ) (Dk : MatrixStage k) :
    extendDensity k Dk k = Dk := by
  simp [extendDensity, restrictDensityTo, partialTraceIter]

/-! ### Iteration law needed below the selected stage

The desired lower-stage identity says that restricting from `k` to `n` is the
same as first restricting from `k` to `n+1`, then taking one more normalized
partial trace.  Its proof should be induction on the remaining depth, with
the casts normalized using `Nat.add_sub_cancel'` / `omega`.  It is kept as an
explicit proposition here until that dependent-index proof is kernel checked.
-/

def RestrictionSuccessorLaw : Prop :=
  ∀ (n k : ℕ) (hn : n < k) (Dk : MatrixStage k),
    restrictDensityTo n k (Nat.le_of_lt hn) Dk =
      normalizedPartialTraceStep n
        (restrictDensityTo (n + 1) k (by omega) Dk)

/-! ### Upper-tail reduction

The upper-tail family equation reduces to the one-step left-inverse theorem
already owned by `MatrixStagePartialTrace`, after exposing the successor law
for `rawMap`.  This proposition isolates the exact coercion statement rather
than pretending Lean has discharged it by definitional unfolding.
-/

def RawMapSuccessorLaw : Prop :=
  ∀ (k n : ℕ) (hn : k ≤ n) (Dk : MatrixStage k),
    rawMap (Nat.le_trans hn (Nat.le_succ n)) Dk =
      concreteStep n (rawMap hn Dk)

theorem upperTail_partialTrace_step
    (hRaw : RawMapSuccessorLaw) (k n : ℕ) (hn : k < n)
    (Dk : MatrixStage k) :
    extendDensity k Dk n =
      normalizedPartialTraceStep n (extendDensity k Dk (n + 1)) := by
  have hsucc : k < n + 1 := by omega
  rw [show extendDensity k Dk n = rawMap (Nat.le_of_lt hn) Dk by
        simp [extendDensity, Nat.not_le_of_gt hn]]
  rw [show extendDensity k Dk (n + 1) = rawMap (Nat.le_of_lt hsucc) Dk by
        simp [extendDensity, Nat.not_le_of_gt hsucc]]
  rw [hRaw k n (Nat.le_of_lt hn) Dk]
  exact (normalizedPartialTraceStep_concreteStep n _).symm

/-! This is a conventional implication theorem, not a packaged certificate:
the only remaining mathematical proof input is `RestrictionSuccessorLaw`;
the raw tail law is exposed separately above. -/

theorem extendDensity_partialTraceCompatible
    (hRestrict : RestrictionSuccessorLaw)
    (hRaw : RawMapSuccessorLaw)
    (k : ℕ) (Dk : MatrixStage k) :
    PartialTraceCompatible (extendDensity k Dk) := by
  intro n
  by_cases hnk : n < k
  · -- The dependent cast calculation in this branch is exactly
    -- `RestrictionSuccessorLaw`; the equality `n+1 ≤ k` chooses the same
    -- lower branch of `extendDensity` on the right.
    have hle : n + 1 ≤ k := by omega
    simp only [extendDensity, dif_pos (Nat.le_of_lt hnk), dif_pos hle]
    exact hRestrict n k hnk Dk
  · by_cases hkn : k < n
    · exact upperTail_partialTrace_step hRaw k n hkn Dk
    · have hEq : n = k := by omega
      subst n
      rw [extendDensity_at_selected_stage]
      -- At the boundary, the upper family value is one successor embedding;
      -- normalized partial trace cancels it by the existing left-inverse law.
      rw [show extendDensity k Dk (k + 1) =
          rawMap (Nat.le_succ k) Dk by simp [extendDensity]]
      rw [hRaw k k le_rfl Dk]
      exact (normalizedPartialTraceStep_concreteStep k Dk).symm

end InfoGeometry.QuantumContext.ChosenStageBackwardDensityCandidate

end
