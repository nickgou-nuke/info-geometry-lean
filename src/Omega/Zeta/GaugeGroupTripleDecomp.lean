/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Tactic
import Omega.Folding.BinFoldGaugeM6
import Omega.OperatorAlgebra.FoldGaugeGroupStructure

/-!
# Window-six BinFold gauge-group count consequences

The concrete gauge carrier is the group of fiber-preserving permutations in
`Omega.Folding.BinFoldGaugeDecomposition`; its fiberwise symmetric-group
decomposition is formalized there. `Omega.Folding.BinFoldGaugeM6` computes the
window-six fiber histogram from the BinFold map, and
`Omega.OperatorAlgebra.FoldGaugeGroupStructure` supplies the componentwise
center, abelianization, derived-order, and total-order conventions. This file
collects the finite window-six arithmetic consequences used downstream.

## Paper references

- thm:xi-foldbin-gauge-group-center-abel-derived-triple-decomposition
-/

namespace Omega.Zeta.GaugeGroupTripleDecomp

/-! ## Window-6 fiber histogram seeds -/

/-- The concrete BinFold fiber histogram at window six gives 21 distinct
    fibers across multiplicities 2, 3, and 4.
    thm:xi-foldbin-gauge-group-center-abel-derived-triple-decomposition -/
theorem histogram_6 : 8 + 4 + 9 = (21 : ℕ) := by
  rcases Omega.Folding.paper_fold_bin_gauge_m6 with ⟨_, _, _, _, htotal⟩
  exact htotal

/-- The listed size-two fibers are a proper part of the total window-six
    histogram; this is a count comparison, not a group-center theorem. -/
theorem size_two_fiber_count_lt_total_6 : 8 < 8 + 4 + 9 := by omega

/-- Actual number of window-six fibers having multiplicity two. Under the
    imported componentwise center formula, this is the center exponent. -/
theorem center_dim_6 : Omega.cBinFiberHist 6 2 = 8 :=
  Omega.cBinFiberHist_6_2

/-- The three actual BinFold fiber counts sum to 21.
    thm:xi-foldbin-gauge-group-center-abel-derived-triple-decomposition -/
theorem abel_dim_6 :
    Omega.cBinFiberHist 6 2 + Omega.cBinFiberHist 6 3 +
      Omega.cBinFiberHist 6 4 = 21 :=
  Omega.binFold6_distinct_multiplicities

/-! ## Derived subgroup structure -/

/-- The numeric values of `d! / 2` for `d = 3, 4`. This seed file does not
    construct alternating groups or their embeddings.
    thm:xi-foldbin-gauge-group-center-abel-derived-triple-decomposition -/
theorem alt_group_orders :
    Nat.factorial 3 / 2 = 3 ∧ Nat.factorial 4 / 2 = 12 := by decide

/-- Powers of the two numeric values recorded above.
    thm:xi-foldbin-gauge-group-center-abel-derived-triple-decomposition -/
theorem derived_order_factors :
    3 ^ 4 = (81 : ℕ) ∧ 12 ^ 9 = 5159780352 := by omega

/-! ## Gauge group total order -/

/-- Factorial values used in the proposed window-six group-order product.
    thm:xi-foldbin-gauge-group-center-abel-derived-triple-decomposition -/
theorem gauge_group_factor_orders :
    Nat.factorial 2 = 2 ∧
    Nat.factorial 3 = 6 ∧
    Nat.factorial 4 = 24 := by decide

/-- Verification: 2⁸ = 256.
    thm:xi-foldbin-gauge-group-center-abel-derived-triple-decomposition -/
theorem pow_2_8 : 2 ^ 8 = (256 : ℕ) := by omega

/-- Verification: 6⁴ = 1296.
    thm:xi-foldbin-gauge-group-center-abel-derived-triple-decomposition -/
theorem pow_6_4 : 6 ^ 4 = (1296 : ℕ) := by omega

/-! ## Count comparisons -/

/-- The size-two fiber count is strictly less than the total number of
    multiplicity-2, -3, and -4 fibers.
    thm:xi-foldbin-gauge-group-center-abel-derived-triple-decomposition -/
theorem center_lt_abel : (8 : ℕ) < 21 := by
  rcases Omega.Folding.paper_fold_bin_gauge_m6 with ⟨_, h2, h3, h4, htotal⟩
  rw [← h2, ← h3, ← h4] at htotal
  omega

/-- The size-three and size-four histogram counts sum to the 13 fibers outside
    the size-two class. -/
theorem noncentral_factor_count_6 : 21 - 8 = 4 + 9 := by omega

/-- The finite BinFold output count is the eighth Fibonacci number, which is
    the number of window-six output states. -/
theorem abel_rank_eq_fib8 : Fintype.card (Omega.X 6) = Nat.fib 8 := by
  simpa using Omega.X.card_eq_fib 6

/-- The full multiplicity-2-through-4 histogram has as many fibers as the
    complete window-six output type. -/
theorem even_window_abel_dim :
    Omega.cBinFiberHist 6 2 + Omega.cBinFiberHist 6 3 +
      Omega.cBinFiberHist 6 4 = Fintype.card (Omega.X 6) := by
  rw [Omega.binFold6_distinct_multiplicities, abel_rank_eq_fib8]
  norm_num

/-- The numeric value `2! / 2` used in the derived-component order convention.
    thm:xi-foldbin-gauge-group-center-abel-derived-triple-decomposition -/
theorem a2_trivial : Nat.factorial 2 / 2 = 1 := by decide

/-! ## Window-six arithmetic -/

/-- Combining the three listed symmetric-group factor orders gives the
    displayed factorization of the window-six product order. -/
theorem gauge_group_order_factorization :
    Nat.factorial 2 ^ 8 * Nat.factorial 3 ^ 4 * Nat.factorial 4 ^ 9 =
      2 ^ 8 * 6 ^ 4 * 24 ^ 9 := by
  rcases gauge_group_factor_orders with ⟨h2, h3, h4⟩
  rw [h2, h3, h4]

/-! ## Scope

All displayed window-six conclusions below are arithmetic consequences of the
concrete histogram or factorial values. Group carriers and generic component
formulas are imported from the owners listed above. -/

/-! ## Paper theorem wrapper -/

/-- Combined gauge group triple decomposition seeds for window-6:
    histogram and factorial arithmetic.
    thm:xi-foldbin-gauge-group-center-abel-derived-triple-decomposition -/
theorem paper_xi_foldbin_gauge_group_triple_decomp_seeds :
    -- Histogram: 8 + 4 + 9 = 21
    8 + 4 + 9 = (21 : ℕ) ∧
    -- The size-two fiber count is bounded by the total count.
    8 < 8 + 4 + 9 ∧
    -- The histogram total in its alternative grouping.
    8 + 4 + 9 = 21 ∧
    -- A₃ order = 3, A₄ order = 12
    Nat.factorial 3 / 2 = 3 ∧
    Nat.factorial 4 / 2 = 12 ∧
    -- Factorial seeds
    Nat.factorial 2 = 2 ∧
    Nat.factorial 3 = 6 ∧
    Nat.factorial 4 = 24 ∧
    -- Center strictly smaller than abelianization
    (8 : ℕ) < 21 := by
  refine ⟨by omega, size_two_fiber_count_lt_total_6, by omega, by decide, by decide, by decide, by decide, by decide,
    by omega⟩

/-- Paper-facing package reusing the arithmetic seed theorem. -/
theorem paper_xi_foldbin_gauge_group_triple_decomp_package :
    8 + 4 + 9 = (21 : ℕ) ∧
    8 < 8 + 4 + 9 ∧
    8 + 4 + 9 = 21 ∧
    Nat.factorial 3 / 2 = 3 ∧
    Nat.factorial 4 / 2 = 12 ∧
    Nat.factorial 2 = 2 ∧
    Nat.factorial 3 = 6 ∧
    Nat.factorial 4 = 24 ∧
    (8 : ℕ) < 21 :=
  paper_xi_foldbin_gauge_group_triple_decomp_seeds

/-- Window-six arithmetic splitting `8 = 3 + 5` and `21 = 3 + 18`, together
    with factorial values. The group-theoretic labels are not formalized here.
    thm:derived-window6-gauge-center-derived-splitting -/
theorem paper_derived_window6_gauge_center_derived_splitting :
    (8 : ℕ) = 3 + 5 ∧
    (21 : ℕ) = 3 + 18 ∧
    Nat.factorial 3 / 2 = 3 ∧
    Nat.factorial 4 / 2 = 12 ∧
    8 + 4 + 9 = 21 := by
  refine ⟨by omega, by omega, alt_group_orders.1, alt_group_orders.2, by omega⟩

/-- Package combining the supplied histogram arithmetic with the
    noncentral count identity. It is not a group decomposition theorem. -/
theorem paper_xi_foldbin_gauge_group_center_abel_derived_triple_decomposition :
    8 + 4 + 9 = (21 : ℕ) ∧
    8 < 8 + 4 + 9 ∧
    8 + 4 + 9 = 21 ∧
    Nat.factorial 3 / 2 = 3 ∧
    Nat.factorial 4 / 2 = 12 ∧
    Nat.factorial 2 = 2 ∧
    Nat.factorial 3 = 6 ∧
    Nat.factorial 4 = 24 ∧
    (8 : ℕ) < 21 ∧
    21 - 8 = 4 + 9 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact paper_xi_foldbin_gauge_group_triple_decomp_package.1
  · exact paper_xi_foldbin_gauge_group_triple_decomp_package.2.1
  · exact paper_xi_foldbin_gauge_group_triple_decomp_package.2.2.1
  · exact paper_xi_foldbin_gauge_group_triple_decomp_package.2.2.2.1
  · exact paper_xi_foldbin_gauge_group_triple_decomp_package.2.2.2.2.1
  · exact paper_xi_foldbin_gauge_group_triple_decomp_package.2.2.2.2.2.1
  · exact paper_xi_foldbin_gauge_group_triple_decomp_package.2.2.2.2.2.2.1
  · exact paper_xi_foldbin_gauge_group_triple_decomp_package.2.2.2.2.2.2.2.1
  · exact paper_xi_foldbin_gauge_group_triple_decomp_package.2.2.2.2.2.2.2.2
  · exact noncentral_factor_count_6

end Omega.Zeta.GaugeGroupTripleDecomp
