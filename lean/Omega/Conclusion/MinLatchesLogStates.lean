/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Tactic

/-!
# Minimum latches equals ceiling log₂ of states

For a sequential transducer π with s(π) states, the minimum number of
latch bits m(π) needed for a synchronous Boolean circuit realization
satisfies m(π) = ⌈log₂ s(π)⌉.

We verify the clog₂ seed values and the encoding bound.
-/

namespace Omega.Conclusion.MinLatchesLogStates

/-! ## General binary encoding theorem

The finite seed checks below verify examples only.  The following statements give the
general arithmetic characterization of the least number of binary digits needed to encode
`n` states.  They do not assert a circuit-realization theorem.
-/

/-- `Nat.clog 2 n` is at most `m` exactly when `n` states fit in `m` binary digits. -/
theorem binary_encoding_iff_clog_bound (n m : ℕ) :
    Nat.clog 2 n ≤ m ↔ n ≤ 2 ^ m :=
  Nat.clog_le_iff_le_pow (by decide : 1 < 2)

/-- The ceiling binary logarithm is the least exponent whose power of two accommodates `n`. -/
theorem binary_encoding_minimality (n : ℕ) :
    n ≤ 2 ^ Nat.clog 2 n ∧
      ∀ m, m < Nat.clog 2 n → ¬ n ≤ 2 ^ m := by
  constructor
  · exact (binary_encoding_iff_clog_bound n (Nat.clog 2 n)).mp le_rfl
  · intro m hm hfits
    have hlog : Nat.clog 2 n ≤ m :=
      (binary_encoding_iff_clog_bound n m).mpr hfits
    omega

/-! ## Seed values for Nat.clog 2 -/

/-- Nat.clog 2 seed values: ⌈log₂ 1⌉=0, ⌈log₂ 2⌉=1, ⌈log₂ 3⌉=2,
    ⌈log₂ 4⌉=2, ⌈log₂ 5⌉=3, ⌈log₂ 8⌉=3, ⌈log₂ 9⌉=4.
    prop:conclusion-min-latches-equals-log-states -/
theorem paper_conclusion_min_latches_log_states :
    Nat.clog 2 1 = 0 ∧ Nat.clog 2 2 = 1 ∧ Nat.clog 2 3 = 2 ∧
    Nat.clog 2 4 = 2 ∧ Nat.clog 2 5 = 3 ∧ Nat.clog 2 8 = 3 ∧
    Nat.clog 2 9 = 4 := by
  refine ⟨by decide, by decide, by decide,
          by decide, by decide, by decide, by decide⟩

/-- The encoding bound: s states fit in m = ⌈log₂ s⌉ bits, i.e. s ≤ 2^m.
    Verified for the seed values.
    prop:conclusion-min-latches-equals-log-states -/
theorem clog_encoding_bound :
    1 ≤ 2 ^ Nat.clog 2 1 ∧ 2 ≤ 2 ^ Nat.clog 2 2 ∧
    3 ≤ 2 ^ Nat.clog 2 3 ∧ 4 ≤ 2 ^ Nat.clog 2 4 ∧
    5 ≤ 2 ^ Nat.clog 2 5 ∧ 8 ≤ 2 ^ Nat.clog 2 8 ∧
    9 ≤ 2 ^ Nat.clog 2 9 := by
  refine ⟨by decide, by decide, by decide,
          by decide, by decide, by decide, by decide⟩

/-- Tightness: reducing m by 1 no longer fits s states.
    Verified for s ∈ {3, 5, 9} (non-power-of-2 cases).
    prop:conclusion-min-latches-equals-log-states -/
theorem clog_tightness :
    ¬(3 ≤ 2 ^ (Nat.clog 2 3 - 1)) ∧
    ¬(5 ≤ 2 ^ (Nat.clog 2 5 - 1)) ∧
    ¬(9 ≤ 2 ^ (Nat.clog 2 9 - 1)) := by
  refine ⟨by decide, by decide, by decide⟩

/-- Extended clog seed: ⌈log₂ 16⌉=4, ⌈log₂ 17⌉=5, ⌈log₂ 21⌉=5 (|X_6|=21),
    ⌈log₂ 32⌉=5, ⌈log₂ 33⌉=6.
    prop:conclusion-min-latches-equals-log-states -/
theorem clog_extended_seeds :
    Nat.clog 2 16 = 4 ∧ Nat.clog 2 17 = 5 ∧
    Nat.clog 2 21 = 5 ∧ Nat.clog 2 32 = 5 ∧ Nat.clog 2 33 = 6 := by
  refine ⟨by decide, by decide, by decide,
          by decide, by decide⟩

/-- Encoding bound for extended seeds.
    prop:conclusion-min-latches-equals-log-states -/
theorem clog_encoding_bound_extended :
    21 ≤ 2 ^ Nat.clog 2 21 ∧ 33 ≤ 2 ^ Nat.clog 2 33 := by
  refine ⟨by decide, by decide⟩

/-- Paper package: min-latches-log-states full seeds.
    prop:conclusion-min-latches-equals-log-states -/
theorem paper_conclusion_min_latches_full :
    Nat.clog 2 1 = 0 ∧ Nat.clog 2 2 = 1 ∧ Nat.clog 2 3 = 2 ∧
    Nat.clog 2 4 = 2 ∧ Nat.clog 2 5 = 3 ∧ Nat.clog 2 8 = 3 ∧
    Nat.clog 2 9 = 4 ∧ Nat.clog 2 21 = 5 ∧ Nat.clog 2 33 = 6 := by
  refine ⟨by decide, by decide, by decide,
          by decide, by decide, by decide,
          by decide, by decide, by decide⟩

end Omega.Conclusion.MinLatchesLogStates
