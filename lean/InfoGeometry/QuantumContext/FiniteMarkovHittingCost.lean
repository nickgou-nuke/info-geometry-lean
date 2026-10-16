/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.FiniteMarkovTransitionKernel
import InfoGeometry.QuantumContext.FiniteMarkovDirichletApproximation

/-!
# Finite Markov first-hit costs

This file records the bounded cost of a finite path up to its first visit to
a target and identifies one Bellman step with integration against the existing
finite transition kernel. It does not yet identify a multi-step trajectory
integral with the Bellman approximants.
-/

namespace InfoGeometry.QuantumContext.FiniteMarkovHittingCost

open MeasureTheory ProbabilityTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The first-hit cost along a finite path, stopped at the first target visit. -/
def truncatedFirstHitCost (target : ι) : List ι → ℝ
  | [] => 0
  | state :: tail =>
      if state = target then 0 else 1 + truncatedFirstHitCost target tail

omit [Fintype ι] in
theorem truncatedFirstHitCost_nonneg (target : ι) (path : List ι) :
    0 ≤ truncatedFirstHitCost target path := by
  induction path with
  | nil => simp [truncatedFirstHitCost]
  | cons state tail ih =>
      simp only [truncatedFirstHitCost]
      split
      · norm_num
      · linarith

omit [Fintype ι] in
theorem truncatedFirstHitCost_le_length (target : ι) (path : List ι) :
    truncatedFirstHitCost target path ≤ path.length := by
  induction path with
  | nil => simp [truncatedFirstHitCost]
  | cons state tail ih =>
      simp only [truncatedFirstHitCost, List.length_cons]
      split
      · positivity
      · have hnonneg := truncatedFirstHitCost_nonneg target tail
        norm_num at *
        linarith

/-- Enumerate a finite Markov history in chronological order, including its
initial and final states. A history through time `n` therefore contributes
`n + 1` entries. -/
def finiteHistoryToList (n : ℕ) (history : Π _ : Finset.Iic n, ι) : List ι :=
  List.ofFn (fun k : Fin (n + 1) =>
    history ⟨k.val, Finset.mem_Iic.mpr (Nat.le_of_lt_succ k.isLt)⟩)

/-- Reindex the states after time zero as a fresh history starting at the
first successor. -/
def finiteHistoryTail {n : ℕ} (history : Π _ : Finset.Iic (n + 1), ι) :
    Π _ : Finset.Iic n, ι :=
  fun k => history ⟨k.val + 1,
    Finset.mem_Iic.mpr (Nat.succ_le_succ (Finset.mem_Iic.mp k.2))⟩

omit [Fintype ι] [DecidableEq ι] in
/-- The chronological list of a finite history splits into its initial state
and the chronological list of the shifted successor history. -/
theorem finiteHistoryToList_succ {n : ℕ}
    (history : Π _ : Finset.Iic (n + 1), ι) :
    finiteHistoryToList (n + 1) history =
      history ⟨0, Finset.mem_Iic.mpr (Nat.zero_le _)⟩ ::
        finiteHistoryToList n (finiteHistoryTail history) := by
  let head : ι := history ⟨0, Finset.mem_Iic.mpr (Nat.zero_le _)⟩
  let tail : Fin (n + 1) → ι := fun k =>
    finiteHistoryTail history
      ⟨k.val, Finset.mem_Iic.mpr (Nat.le_of_lt_succ k.isLt)⟩
  have hcoordinates :
      (fun k : Fin (n + 2) =>
        history ⟨k.val, Finset.mem_Iic.mpr (Nat.le_of_lt_succ k.isLt)⟩) =
        Fin.cons head tail := by
    funext k
    refine Fin.cases ?_ ?_ k
    · rfl
    · intro j
      simp [head, tail, finiteHistoryTail]
  change List.ofFn
      (fun k : Fin (n + 2) =>
        history ⟨k.val, Finset.mem_Iic.mpr (Nat.le_of_lt_succ k.isLt)⟩) = _
  rw [hcoordinates, List.ofFn_cons]
  rfl

omit [Fintype ι] in
/-- The first-hit cost obeys its literal pathwise first-step recursion on an
inclusive finite history. -/
theorem truncatedFirstHitCost_finiteHistory_succ {n : ℕ}
    (target : ι) (history : Π _ : Finset.Iic (n + 1), ι) :
    truncatedFirstHitCost target (finiteHistoryToList (n + 1) history) =
      if history ⟨0, Finset.mem_Iic.mpr (Nat.zero_le _)⟩ = target then 0 else
        1 + truncatedFirstHitCost target
          (finiteHistoryToList n (finiteHistoryTail history)) := by
  rw [finiteHistoryToList_succ]
  rfl

open InfoGeometry.QuantumContext.FiniteMarkovTransitionKernel
open InfoGeometry.QuantumContext.FiniteMarkovDirichletApproximation

/-- Away from the target, the next Bellman iterate is one unit of current
cost plus the real expected previous iterate after one transition. -/
theorem firstHitApproximation_succ_eq_transition_expectation
    (P : Matrix ι ι ℝ) (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (target : ι) (n : ℕ) (i : ι) (hi : i ≠ target) :
    firstHitApproximation P target (n + 1) i =
      1 + ∫ j, firstHitApproximation P target n j ∂transitionKernel P hP i := by
  rw [firstHitApproximation_succ_of_ne P target n i hi,
    transitionKernel_integral_eq_mulVec P hP i
      (firstHitApproximation P target n)]

/-- The Bellman value at the target remains zero at every successor horizon. -/
theorem firstHitApproximation_succ_eq_target
    (P : Matrix ι ι ℝ) (target : ι) (n : ℕ) :
    firstHitApproximation P target (n + 1) target = 0 :=
  firstHitApproximation_target P target (n + 1)

end InfoGeometry.QuantumContext.FiniteMarkovHittingCost
