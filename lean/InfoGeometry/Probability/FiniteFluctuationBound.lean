/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ThermodynamicChiralGraphCalculus
import InfoGeometry.Inference.FiniteRelativeEntropyEquality
import InfoGeometry.Math.Convexity

/-!
# Expected entropy production and work from a finite fluctuation law

## Overview

The existing `IntegralFluctuationLaw` consists of two strictly positive,
normalized probability functions on the same finite sample space. Its entropy
production is the actual logarithm of their likelihood ratio, and its integral
fluctuation identity has already been proved from those probabilities.

This owner derives the mean-production bound and its equality case, then
transports them through an explicit pathwise work/free-energy/correction
identity. The generic exponential-moment consequence also permits zero
weights. It reuses the existing negative-log Jensen theorem.

## Key results

- `mean_nonneg_of_exp_neg_le_one`: a finite exponential-moment bound implies a
  nonnegative mean, with nonnegative normalized weights.
- `expected_entropyProduction_eq_zero_iff`: zero mean production is equivalent
  to equality of the full forward and backward probability functions.
- `corrected_expected_work_bound`: the precise correction to the mean-work
  inequality, with an explicit positive inverse temperature.
- `corrected_expected_work_eq_iff`: saturation is characterized by equality of
  the two probability functions, not assumed attainability of a process.

## Table of contents

1. Finite exponential moments.
2. Existing likelihood laws and equality.
3. Work ledgers and the zero-correction specialization.

## References

The finite likelihood and relative-entropy owners supply the mathematical
carriers. These consequences do not construct a stochastic process, filtration,
stopping time, reverse dynamics, or optional-stopping theorem. A physical
stopping-time application must independently establish the pathwise law.
-/

noncomputable section

namespace InfoGeometry.Probability.FiniteFluctuationBound

open scoped BigOperators
open InfoGeometry.Canonical.ThermodynamicChiralGraphCalculus.DirectedThermoGraph

/-- Existing finite Jensen gives the mean consequence even when some weights
vanish. Constructing the exponential-moment bound remains a separate premise. -/
theorem mean_nonneg_of_exp_neg_le_one {ι : Type*} [Fintype ι]
    (p X : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hp_sum : ∑ i, p i = 1)
    (hExp : ∑ i, p i * Real.exp (-X i) ≤ 1) :
    0 ≤ ∑ i, p i * X i := by
  have hNonneg : 0 ≤ ∑ i, p i * Real.exp (-X i) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hp i) (Real.exp_pos _).le
  have hJensen := InfoGeometry.Math.Convexity.neg_log_jensen_sum
    p hp hp_sum (fun i => Real.exp (-X i)) (fun _ => Real.exp_pos _)
  have hLog : 0 ≤ -Real.log (∑ i, p i * Real.exp (-X i)) :=
    neg_nonneg.mpr (Real.log_nonpos hNonneg hExp)
  exact hLog.trans (by simpa only [Real.log_exp, neg_neg] using hJensen)

variable {Ω : Type} [Fintype Ω]

/-- The previously proved likelihood fluctuation identity has nonnegative mean
entropy production. No second-law inequality is included as a structure field. -/
theorem expected_entropyProduction_nonneg (L : IntegralFluctuationLaw Ω) :
    0 ≤ L.expectation L.entropyProduction := by
  exact mean_nonneg_of_exp_neg_le_one L.forwardProbability L.entropyProduction
    (fun ω => (L.forward_positive ω).le) L.forward_normalized
    (le_of_eq (integral_fluctuation_theorem L))

/-- Strict positivity of both probabilities supplies the exact relative-entropy
equality case without a convention for logarithms on a missing support. -/
theorem expected_entropyProduction_eq_zero_iff (L : IntegralFluctuationLaw Ω) :
    L.expectation L.entropyProduction = 0 ↔
      L.forwardProbability = L.backwardProbability := by
  change InfoGeometry.Inference.finiteRelativeEntropy
    L.forwardProbability L.backwardProbability = 0 ↔ _
  exact InfoGeometry.Inference.finiteRelativeEntropy_eq_zero_iff
    L.forwardProbability L.backwardProbability L.forward_positive
    L.backward_positive L.forward_normalized L.backward_normalized

/-- The pathwise work identity becomes an exact finite expectation ledger. -/
theorem expected_entropyProduction_work_ledger (L : IntegralFluctuationLaw Ω)
    (β : ℝ) (W ΔF δ : Ω → ℝ)
    (hPath : ∀ ω, L.entropyProduction ω = β * (W ω - ΔF ω) + δ ω) :
    L.expectation L.entropyProduction =
      β * (L.expectation W - L.expectation ΔF) + L.expectation δ := by
  unfold IntegralFluctuationLaw.expectation
  calc
    (∑ ω, L.forwardProbability ω * L.entropyProduction ω) =
        ∑ ω, (β * (L.forwardProbability ω * W ω) -
          β * (L.forwardProbability ω * ΔF ω) + L.forwardProbability ω * δ ω) := by
      apply Finset.sum_congr rfl
      intro ω _
      rw [hPath ω]
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum]
      ring

/-- The correction has a fixed sign and denominator once work is defined as
work supplied to the system and the pathwise production identity is specified. -/
theorem corrected_expected_work_bound (L : IntegralFluctuationLaw Ω)
    (β : ℝ) (hβ : 0 < β) (W ΔF δ : Ω → ℝ)
    (hPath : ∀ ω, L.entropyProduction ω = β * (W ω - ΔF ω) + δ ω) :
    -L.expectation δ / β ≤ L.expectation W - L.expectation ΔF := by
  have hProduction := expected_entropyProduction_nonneg L
  rw [expected_entropyProduction_work_ledger L β W ΔF δ hPath] at hProduction
  apply (div_le_iff₀ hβ).2
  nlinarith

/-- Equality of the work bound is an exact likelihood criterion; this theorem
does not construct a process attaining it under additional physical controls. -/
theorem corrected_expected_work_eq_iff (L : IntegralFluctuationLaw Ω)
    (β : ℝ) (hβ : 0 < β) (W ΔF δ : Ω → ℝ)
    (hPath : ∀ ω, L.entropyProduction ω = β * (W ω - ΔF ω) + δ ω) :
    L.expectation W - L.expectation ΔF = -L.expectation δ / β ↔
      L.forwardProbability = L.backwardProbability := by
  rw [← expected_entropyProduction_eq_zero_iff L,
    expected_entropyProduction_work_ledger L β W ΔF δ hPath]
  rw [eq_div_iff hβ.ne']
  constructor <;> intro h <;> nlinarith

/-- A zero pathwise correction specializes the same actual likelihood law to
the usual mean-work lower bound. -/
theorem expected_work_bound_of_zero_correction (L : IntegralFluctuationLaw Ω)
    (β : ℝ) (hβ : 0 < β) (W ΔF : Ω → ℝ)
    (hPath : ∀ ω, L.entropyProduction ω = β * (W ω - ΔF ω)) :
    L.expectation ΔF ≤ L.expectation W := by
  have hProduction := expected_entropyProduction_nonneg L
  have hLedger := expected_entropyProduction_work_ledger L β W ΔF (fun _ => 0)
    (fun ω => by simpa only [add_zero] using hPath ω)
  have hZero : L.expectation (fun _ => 0) = 0 := by
    simp only [IntegralFluctuationLaw.expectation, mul_zero, Finset.sum_const_zero]
  rw [hLedger, hZero, add_zero] at hProduction
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hβ).mp hProduction)

/-- In the zero-correction specialization, mean-work saturation is equivalent
to equality of the forward and backward path distributions. -/
theorem expected_work_eq_iff_of_zero_correction (L : IntegralFluctuationLaw Ω)
    (β : ℝ) (hβ : 0 < β) (W ΔF : Ω → ℝ)
    (hPath : ∀ ω, L.entropyProduction ω = β * (W ω - ΔF ω)) :
    L.expectation W = L.expectation ΔF ↔
      L.forwardProbability = L.backwardProbability := by
  have h := corrected_expected_work_eq_iff L β hβ W ΔF (fun _ => 0)
    (fun ω => by simpa only [add_zero] using hPath ω)
  simpa only [IntegralFluctuationLaw.expectation, mul_zero, Finset.sum_const_zero,
    neg_zero, zero_div, sub_eq_zero] using h

end InfoGeometry.Probability.FiniteFluctuationBound

end
