/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Adelic.NarainTamagawa
import Mathlib.NumberTheory.ZetaValues

/-!
# Reciprocal-square partial-sum limit

This capstone is an analytic series result. It does not identify the series
with an adelic measure or establish a Tamagawa volume.
-/

namespace InfoGeometry.Canonical.NarainTamagawaCapstone

open InfoGeometry.Adelic.NarainTamagawa
open Filter
open scoped BigOperators Topology

/-- The finite reciprocal-square partial sums converge to `π² / 6`.

The proof uses the owner summability result and Mathlib's exact value of the
series. -/
theorem inverse_square_partial_sums_tendsto :
    Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N, (1 : ℝ) / (n : ℝ) ^ 2)
      atTop (𝓝 (Real.pi ^ 2 / 6)) := by
  have hsum : HasSum (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2)
      (∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2) :=
    inverse_square_series_summable.hasSum
  have hvalue := hasSum_zeta_two.tsum_eq
  simpa only [← hvalue] using hsum.tendsto_sum_nat

end InfoGeometry.Canonical.NarainTamagawaCapstone
