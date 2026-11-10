import Mathlib.NumberTheory.ZetaValues

/-!
# Zeta-series input for the Narain/Tamagawa avenue

The repository does not currently construct an adelic measure space or prove a
Tamagawa-volume formula for `SL₂`. This file therefore makes no claim about
such a volume. It records a genuine analytic input that is sometimes relevant
to volume calculations: convergence of the reciprocal-square series.
-/

namespace InfoGeometry.Adelic.NarainTamagawa

/-- The reciprocal-square series over the naturals is summable in `ℝ`.

The value of its sum is established in Mathlib as `hasSum_zeta_two`; this
summability result alone is not an adelic or Tamagawa-volume computation. -/
theorem inverse_square_series_summable :
    Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) := by
  exact hasSum_zeta_two.summable

end InfoGeometry.Adelic.NarainTamagawa
