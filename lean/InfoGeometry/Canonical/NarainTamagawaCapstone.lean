/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

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

The proof follows from the owner's exact `HasSum` statement. -/
theorem inverse_square_partial_sums_tendsto :
    Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N, (1 : ℝ) / (n : ℝ) ^ 2)
      atTop (𝓝 (Real.pi ^ 2 / 6)) := by
  have hsum := inverse_square_series_summable.1
  exact hsum.tendsto_sum_nat

end InfoGeometry.Canonical.NarainTamagawaCapstone
