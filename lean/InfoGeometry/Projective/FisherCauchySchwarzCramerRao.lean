/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebraic.CartanExponentialFamily

/-!
# Cauchy–Schwarz for the finite Fisher covariance and Cramér–Rao

Closing lemma for the projective (L1) information-geometric lane.  The finite
Cartan exponential-family owner defines the centered Fisher covariance
`fisherCov θ X Y` and proves `fisherCov_self_nonneg`, but the bilinear
Cauchy–Schwarz inequality and the resulting Cramér–Rao readout were missing.

Retrieved context (`docufgtdrdment.pdf` §3.2, `entropy-28-00044` §3;
authority `retrieval_context_only`, never proof evidence) ties the Hessian
Fisher metric to a Cramér–Rao bound.  Here the inequality is proved directly
from the finite weighted Cauchy–Schwarz theorem for the Gibbs weights, with no
analytic or asymptotic assumption.  The parameter-derivative normalization is
an explicit hypothesis (`fisherCov θ X score = 1`), not a derived claim.
-/

noncomputable section

namespace InfoGeometry.Projective.FisherCauchySchwarzCramerRao

open scoped BigOperators
open Finset
open InfoGeometry.Algebraic.CartanExponentialFamily

variable {ι : Type*} [Fintype ι]

/-- Cauchy–Schwarz for the centered Fisher covariance form:
`Cov(X,Y)² ≤ Cov(X,X) · Cov(Y,Y)`. -/
theorem fisherCov_mul_sq_le (θ X Y : ι → ℝ) (hZ : 0 < Z θ) :
    (fisherCov θ X Y) ^ (2 : ℕ) ≤ fisherCov θ X X * fisherCov θ Y Y := by
  let μX : ℝ := expect θ X
  let μY : ℝ := expect θ Y
  unfold fisherCov
  change
    (∑ i : ι, prob θ i * (X i - μX) * (Y i - μY)) ^ (2 : ℕ) ≤
      (∑ i : ι, prob θ i * (X i - μX) * (X i - μX)) *
        (∑ i : ι, prob θ i * (Y i - μY) * (Y i - μY))
  refine sum_sq_le_sum_mul_sum_of_sq_le_mul (s := Finset.univ)
    (r := fun i => prob θ i * (X i - μX) * (Y i - μY))
    (f := fun i => prob θ i * (X i - μX) * (X i - μX))
    (g := fun i => prob θ i * (Y i - μY) * (Y i - μY)) ?_ ?_ ?_
  · intro i hi
    have hsq : 0 ≤ (X i - μX) * (X i - μX) := by nlinarith [sq_nonneg (X i - μX)]
    simpa [mul_assoc] using mul_nonneg (prob_nonneg (θ := θ) hZ i) hsq
  · intro i hi
    have hsq : 0 ≤ (Y i - μY) * (Y i - μY) := by nlinarith [sq_nonneg (Y i - μY)]
    simpa [mul_assoc] using mul_nonneg (prob_nonneg (θ := θ) hZ i) hsq
  · intro i hi
    ring_nf
    exact le_rfl

/-- The Cramér–Rao bound for a normalized score statistic: if the estimator
`X` has unit Fisher covariance with the score, then `1 / I ≤ Var(X)`, where
`I = Cov(score, score)` is the Fisher information.  The zero-information case
is excluded by the positive-information hypothesis. -/
theorem cramer_rao_of_fisherCov_normalization
    (θ X score : ι → ℝ) (hZ : 0 < Z θ)
    (h_norm : fisherCov θ X score = 1)
    (hI : 0 < fisherCov θ score score) :
    1 / fisherCov θ score score ≤ fisherCov θ X X := by
  have hcs := fisherCov_mul_sq_le (θ := θ) X score hZ
  rw [h_norm] at hcs
  have hcs' : (1 : ℝ) ≤ fisherCov θ X X * fisherCov θ score score := by
    simpa using hcs
  exact (div_le_iff₀ hI).2 hcs'

end InfoGeometry.Projective.FisherCauchySchwarzCramerRao
