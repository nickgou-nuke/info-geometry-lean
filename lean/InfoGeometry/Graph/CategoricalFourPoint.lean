/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

/-!
# Four-point additivity diagnostic

The repository's structural-affinity exporter evaluates the three quartet
pair sums and reports largest minus second-largest. This module formalizes that
exact diagnostic over `ℚ`; a zero residual is the four-point additivity
condition. It does not interpret additivity as ancestry or confidence.
-/

namespace InfoGeometry.Graph.CategoricalFourPoint

/-- Largest of the three paired-distance sums for a quartet. -/
def quartetLargest (x y z : ℚ) : ℚ := max x (max y z)

/-- Second-largest of the three paired-distance sums. -/
def quartetSecondLargest (x y z : ℚ) : ℚ :=
  max (min x y) (min (max x y) z)

/-- Exact four-point residual used as a tree-additivity diagnostic. -/
def quartetResidual (x y z : ℚ) : ℚ :=
  quartetLargest x y z - quartetSecondLargest x y z

/-- Total number of unordered four-taxon subsets inspected by the diagnostic. -/
def quartetTotalCount (taxaCount : ℕ) : ℕ := Nat.choose taxaCount 4

/-- The actual finite family of four-taxon subsets of the indexed taxon set. -/
def quartetSubsets (taxaCount : ℕ) : Finset (Finset (Fin taxaCount)) :=
  (Finset.univ : Finset (Fin taxaCount)).powersetCard 4

/-- The finite quartet family has the binomial cardinality used by the
exporter's diagnostic count. -/
theorem quartetSubsets_card (taxaCount : ℕ) :
    (quartetSubsets taxaCount).card = quartetTotalCount taxaCount := by
  rw [quartetSubsets, Finset.card_powersetCard]
  simp [quartetTotalCount]

/-- Number of quartet residuals evaluated when the configured positive cap is
`cap`. The exporter reports no quartets below four taxa and otherwise evaluates
all quartets up to the cap, or exactly `cap` in its deterministic sampling
branch. This count does not model Python's pseudorandom sample itself. -/
def quartetEvaluatedCount (taxaCount cap : ℕ) (_hCap : 0 < cap) : ℕ :=
  if taxaCount < 4 then 0 else min (quartetTotalCount taxaCount) cap

/-- Whether the exporter enters its all-quartets branch rather than its
deterministic-sampling branch. -/
def quartetUsesExhaustiveEvaluation (taxaCount cap : ℕ) : Prop :=
  4 ≤ taxaCount ∧ quartetTotalCount taxaCount ≤ cap

/-- Below four taxa, there are no four-element subsets. -/
theorem quartetTotalCount_eq_zero_of_lt_four {taxaCount : ℕ}
    (h : taxaCount < 4) : quartetTotalCount taxaCount = 0 := by
  unfold quartetTotalCount
  exact Nat.choose_eq_zero_of_lt h

/-- With at least four taxa, a cap at least the total count evaluates every
quartet, matching the exporter's exhaustive branch. -/
theorem quartetEvaluatedCount_eq_total {taxaCount cap : ℕ}
    (hPositiveCap : 0 < cap) (hTaxa : 4 ≤ taxaCount)
    (hCap : quartetTotalCount taxaCount ≤ cap) :
    quartetEvaluatedCount taxaCount cap hPositiveCap = quartetTotalCount taxaCount := by
  unfold quartetEvaluatedCount
  split_ifs with h
  · omega
  · rw [Nat.min_eq_left hCap]

/-- With at least four taxa and a smaller cap, the exporter evaluates exactly
the cap-sized deterministic sample. -/
theorem quartetEvaluatedCount_eq_cap {taxaCount cap : ℕ}
    (hPositiveCap : 0 < cap) (hTaxa : 4 ≤ taxaCount)
    (hCap : cap < quartetTotalCount taxaCount) :
    quartetEvaluatedCount taxaCount cap hPositiveCap = cap := by
  unfold quartetEvaluatedCount
  split_ifs with h
  · omega
  · rw [Nat.min_eq_right (Nat.le_of_lt hCap)]

/-- The evaluated count never exceeds either the number of possible quartets
or the configured cap. -/
theorem quartetEvaluatedCount_le_bounds (taxaCount cap : ℕ) (hCap : 0 < cap) :
    quartetEvaluatedCount taxaCount cap hCap ≤ quartetTotalCount taxaCount ∧
    quartetEvaluatedCount taxaCount cap hCap ≤ cap := by
  by_cases h : taxaCount < 4
  · simp [quartetEvaluatedCount, h, quartetTotalCount_eq_zero_of_lt_four h]
  · simp only [quartetEvaluatedCount, h, ite_false]
    exact ⟨Nat.min_le_left _ _, Nat.min_le_right _ _⟩

theorem quartetSecondLargest_le_largest (x y z : ℚ) :
    quartetSecondLargest x y z ≤ quartetLargest x y z := by
  unfold quartetSecondLargest quartetLargest
  apply max_le
  · exact le_trans (min_le_left x y) (le_max_left x (max y z))
  · exact le_trans (min_le_left (max x y) z)
      (max_le (le_max_left x (max y z))
        (le_trans (le_max_left y z) (le_max_right x (max y z))))

/-- The diagnostic residual is nonnegative for every quartet. -/
theorem quartetResidual_nonneg (x y z : ℚ) :
    0 ≤ quartetResidual x y z := by
  unfold quartetResidual
  exact sub_nonneg.mpr (quartetSecondLargest_le_largest x y z)

/-- The four-point additivity condition is exactly vanishing of the residual:
the largest and second-largest paired sums agree. -/
theorem quartetResidual_eq_zero_iff (x y z : ℚ) :
    quartetResidual x y z = 0 ↔
      quartetLargest x y z = quartetSecondLargest x y z := by
  unfold quartetResidual
  exact sub_eq_zero

end InfoGeometry.Graph.CategoricalFourPoint
