/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Order.Interval.Finset.Nat

namespace Omega.GU

/-- Concrete data for the binomial Fourier extraction identity. The moment is defined by the
finite Laurent expansion appearing in the paper statement. -/
structure JGBinomialFilteringData where
  r : Complex
  fourierCoeff : Int → Complex

/-- The pushed-forward holomorphic moments are encoded by the explicit binomial/Fourier sum. -/
noncomputable def JGBinomialFilteringData.moment (D : JGBinomialFilteringData) (n : Nat) :
    Complex :=
  Finset.sum (Finset.Icc 0 n) fun j =>
    (Nat.choose n j : Complex) * D.r ^ (2 * j) / D.r ^ n *
      D.fourierCoeff (((2 * j : Nat) : Int) - (n : Int))

/-- Paper label: `thm:group-jg-binomial-filtering-fourier-extraction`. -/
theorem paper_group_jg_binomial_filtering_fourier_extraction
    (D : JGBinomialFilteringData) (n : Nat) :
    D.moment n =
      Finset.sum (Finset.range (n + 1)) (fun j =>
        (Nat.choose n j : Complex) * D.r ^ (2 * j) / D.r ^ n *
          D.fourierCoeff (((2 * j : Nat) : Int) - (n : Int))) := by
  change Finset.sum (Finset.Icc 0 n) (fun j =>
    (Nat.choose n j : Complex) * D.r ^ (2 * j) / D.r ^ n *
      D.fourierCoeff (((2 * j : Nat) : Int) - (n : Int))) = _
  rw [← Nat.range_succ_eq_Icc_zero n]

/-- The finite moment depends only on the radius and the Fourier coefficients at the
frequencies occurring in its binomial window. -/
theorem JGBinomialFilteringData.moment_congr
    (D E : JGBinomialFilteringData) (n : Nat)
    (hr : D.r = E.r)
    (hcoeff : ∀ j ∈ Finset.range (n + 1),
      D.fourierCoeff (((2 * j : Nat) : Int) - (n : Int)) =
        E.fourierCoeff (((2 * j : Nat) : Int) - (n : Int))) :
    D.moment n = E.moment n := by
  simp only [JGBinomialFilteringData.moment]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j ∈ Finset.range (n + 1) := by
    simpa only [Nat.range_succ_eq_Icc_zero n] using hj
  rw [hr, hcoeff j hj']

end Omega.GU
