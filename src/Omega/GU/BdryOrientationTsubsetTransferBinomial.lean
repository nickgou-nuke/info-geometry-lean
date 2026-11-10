/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Finset.Powerset

namespace Omega.GU

/-- The number of representatives of size-`t` subsets that contain the first point of a fixed
transposition and omit its second point. Choosing the other `t - 1` elements from the remaining
`k - 2` points gives the finite-set model below. -/
def tSubsetSwapTranspositionCount (k t : Nat) : Nat :=
  (Finset.powersetCard (t - 1) (Finset.range (k - 2))).card

/-- The transfer count is the binomial coefficient counting subsets of the remaining points.
This identifies the concrete finite-set cardinality with its closed form. -/
theorem paper_bdry_orientation_tsubset_transfer_binomial (k t : Nat) :
    tSubsetSwapTranspositionCount k t = Nat.choose (k - 2) (t - 1) := by
  classical
  simp [tSubsetSwapTranspositionCount, Finset.card_powersetCard]

/-- Pascal recursion for the transfer count. For `2 ≤ t`, splitting choices according to
whether they contain a distinguished point gives the two adjacent counts at width `k`. -/
theorem tSubsetSwapTranspositionCount_pascal (k t : Nat)
    (hk : 2 ≤ k) (ht : 2 ≤ t) :
    tSubsetSwapTranspositionCount k t +
      tSubsetSwapTranspositionCount k (t - 1) =
      tSubsetSwapTranspositionCount (k + 1) t := by
  rw [paper_bdry_orientation_tsubset_transfer_binomial,
      paper_bdry_orientation_tsubset_transfer_binomial,
      paper_bdry_orientation_tsubset_transfer_binomial]
  have hk' : k - 2 + 1 = k - 1 := by omega
  have ht' : t - 2 + 1 = t - 1 := by omega
  rw [show k + 1 - 2 = k - 1 by omega,
      show t - 1 - 1 = t - 2 by omega,
      show t - 1 = t - 2 + 1 by omega,
      ← hk', Nat.choose_succ_succ']
  exact Nat.add_comm _ _

end Omega.GU
