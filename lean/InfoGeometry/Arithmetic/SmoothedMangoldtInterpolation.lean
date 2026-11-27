/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Arithmetic.SmoothedMangoldtReal
import InfoGeometry.Analysis.CenteredLogInterpolation

/-!
# Centered Mangoldt interpolation

The uncentered smoothing is affine between adjacent integers. After subtracting
`x * log x`, its interpolation error is exactly the nonnegative logarithmic
chord error. The linear Euler-constant correction cancels. The resulting
explicit inequalities work for both signs of a bound on the centered sum.
-/

noncomputable section

open InfoGeometry.Analysis.CenteredLogInterpolation

namespace InfoGeometry.Arithmetic.PrimeDistributionLaw

/-- Exact centered interpolation, with the error on the positive side. -/
theorem centeredSmoothedMangoldtSum_eq_affine_add_error (N : ℕ) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    centeredSmoothedMangoldtSum ((N : ℝ) + t) =
      (1 - t) * centeredSmoothedMangoldtSum (N : ℝ) +
        t * centeredSmoothedMangoldtSum ((N + 1 : ℕ) : ℝ) +
          logChordError (N : ℝ) t := by
  unfold centeredSmoothedMangoldtSum
  rw [realSmoothedMangoldtSum_eq_affine N t ht0 ht1,
    realSmoothedMangoldtSum_natCast, realSmoothedMangoldtSum_natCast]
  unfold logChordError
  push_cast
  ring

/-- The centered sum lies above the affine interpolation of its integer values. -/
theorem affine_le_centeredSmoothedMangoldtSum (N : ℕ) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - t) * centeredSmoothedMangoldtSum (N : ℝ) +
        t * centeredSmoothedMangoldtSum ((N + 1 : ℕ) : ℝ) ≤
      centeredSmoothedMangoldtSum ((N : ℝ) + t) := by
  rw [centeredSmoothedMangoldtSum_eq_affine_add_error N t ht0 ht1]
  exact le_add_of_nonneg_right (logChordError_nonneg (Nat.cast_nonneg N) ht0 ht1)

/-- Quadratic curvature upper estimate for the centered interpolation error. -/
theorem centeredSmoothedMangoldtSum_le_affine_add_quadratic {N : ℕ}
    (hN : 1 ≤ N) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    centeredSmoothedMangoldtSum ((N : ℝ) + t) ≤
      (1 - t) * centeredSmoothedMangoldtSum (N : ℝ) +
        t * centeredSmoothedMangoldtSum ((N + 1 : ℕ) : ℝ) +
          t * (1 - t) / (2 * (N : ℝ)) := by
  rw [centeredSmoothedMangoldtSum_eq_affine_add_error N t ht0 ht1]
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_one.trans_le hN)
  exact add_le_add le_rfl (logChordError_le_quadratic hNpos ht0 ht1)

/-- Uniform interpolation error at a positive integer cutoff. -/
theorem centeredSmoothedMangoldtSum_le_affine_add_one_div_eight {N : ℕ}
    (hN : 1 ≤ N) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    centeredSmoothedMangoldtSum ((N : ℝ) + t) ≤
      (1 - t) * centeredSmoothedMangoldtSum (N : ℝ) +
        t * centeredSmoothedMangoldtSum ((N + 1 : ℕ) : ℝ) +
          1 / (8 * (N : ℝ)) := by
  rw [centeredSmoothedMangoldtSum_eq_affine_add_error N t ht0 ht1]
  exact add_le_add le_rfl (logChordError_nat_bounds hN ht0 ht1).2

/-- One uniform estimate handles either fixed sign of the centered sum. -/
theorem signed_centeredSmoothedMangoldtSum_le_affine {N : ℕ} (hN : 1 ≤ N)
    {sign : ℝ} (hsign : sign = 1 ∨ sign = -1) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    sign * centeredSmoothedMangoldtSum ((N : ℝ) + t) ≤
      (1 - t) * (sign * centeredSmoothedMangoldtSum (N : ℝ)) +
        t * (sign * centeredSmoothedMangoldtSum ((N + 1 : ℕ) : ℝ)) +
          1 / (8 * (N : ℝ)) := by
  rw [centeredSmoothedMangoldtSum_eq_affine_add_error N t ht0 ht1]
  obtain ⟨hlo, hhi⟩ := logChordError_nat_bounds hN ht0 ht1
  have hbound : 0 ≤ 1 / (8 * (N : ℝ)) := by positivity
  rcases hsign with rfl | rfl <;> nlinarith

/-- For the negative sign the logarithmic error only improves the upper bound. -/
theorem neg_centeredSmoothedMangoldtSum_le_affine (N : ℕ) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    -centeredSmoothedMangoldtSum ((N : ℝ) + t) ≤
      (1 - t) * (-centeredSmoothedMangoldtSum (N : ℝ)) +
        t * (-centeredSmoothedMangoldtSum ((N + 1 : ℕ) : ℝ)) := by
  have h := affine_le_centeredSmoothedMangoldtSum N t ht0 ht1
  linarith

end InfoGeometry.Arithmetic.PrimeDistributionLaw
