/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.NumberTheory.ZetaValues

/-!
# Zeta-series input for the Narain/Tamagawa avenue

The repository does not currently construct an adelic measure space or prove a
Tamagawa-volume formula for `SL₂`. This file therefore makes no claim about
such a volume. It records the exact reciprocal-square sum and its summability,
an analytic input sometimes relevant to volume calculations.
-/

namespace InfoGeometry.Adelic.NarainTamagawa

/-- The reciprocal-square series over the naturals has sum `π² / 6` and is
summable in `ℝ`.

The first component states the exact Basel sum; the second provides the
convergence interface for later analytic arguments. -/
theorem inverse_square_series_summable :
    HasSum (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) (Real.pi ^ 2 / 6) ∧
    Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) := by
  constructor
  · simpa using hasSum_zeta_two
  · exact hasSum_zeta_two.summable

end InfoGeometry.Adelic.NarainTamagawa
