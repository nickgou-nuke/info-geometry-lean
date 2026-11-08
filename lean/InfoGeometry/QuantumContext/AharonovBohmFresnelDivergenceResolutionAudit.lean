/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.AharonovBohmFresnelDivergenceResolution

/-!
# Concrete Integer Examples for Section 120b: Fresnel Quadrature Identities
Target: `InfoGeometry/QuantumContext/AharonovBohmFresnelDivergenceResolutionAudit.lean`

Verifies over `ℤ` (`decide`) that the Brahmagupta–Fibonacci–Fresnel norm partition,
central Yin vanishing, and asymptotic truncation negativity threshold hold on concrete values.
-/

namespace InfoGeometry.QuantumContext.AharonovBohmFresnelAudit

open InfoGeometry.QuantumContext.SorkinFluxQubit

/-- Concrete verification of `I_+ * I_- = G² + H²` for `ψ_+ = (3, 4)` (`I_+ = 25`) and `ψ_- = (1, 2)` (`I_- = 5`):
`G = 11`, `H = 2`, `11^2 + 2^2 = 125 = 25 * 5`. -/
theorem sample_brahmagupta_fibonacci_fresnel_int :
    let ψ_pos : FresnelWave ℤ := ⟨3, 4⟩
    let ψ_neg : FresnelWave ℤ := ⟨1, 2⟩
    FresnelWave.intensity ψ_pos = 25 ∧
    FresnelWave.intensity ψ_neg = 5 ∧
    FresnelWave.yangG ψ_pos ψ_neg = 11 ∧
    FresnelWave.yinH ψ_pos ψ_neg = 2 ∧
    FresnelWave.intensity ψ_pos * FresnelWave.intensity ψ_neg =
      FresnelWave.yangG ψ_pos ψ_neg * FresnelWave.yangG ψ_pos ψ_neg +
      FresnelWave.yinH ψ_pos ψ_neg * FresnelWave.yinH ψ_pos ψ_neg := by
  decide

/-- Concrete equal-input identities and threshold values: `H_asymp = 20` does not exceed `(25 + 25)/2 = 25`, while `H_asymp = 30` does. -/
theorem sample_equal_input_and_asymptotic_threshold_int :
    let ψ₀ : FresnelWave ℤ := ⟨3, 4⟩
    FresnelWave.yinH ψ₀ ψ₀ = 0 ∧
    FresnelWave.abProb ψ₀ ψ₀ 0 1 = 50 ∧
    FresnelWave.abProb ψ₀ ψ₀ 0 (-1) = 50 ∧
    ((25 + 25 - 2 * (20 : ℤ) < 0) = False) ∧
    ((25 + 25 - 2 * (30 : ℤ) < 0) = True) := by
  decide

#print axioms FresnelWave.yang_symmetric_under_slit_swap
#print axioms FresnelWave.yin_skew_symmetric_under_slit_swap
#print axioms FresnelWave.yin_zero_on_equal_inputs
#print axioms FresnelWave.yang_eq_intensity_on_equal_inputs
#print axioms FresnelWave.brahmagupta_fibonacci_fresnel_norm_identity
#print axioms FresnelWave.ab_probability_plus_sum_of_squares
#print axioms FresnelWave.ab_probability_minus_sum_of_squares
#print axioms FresnelWave.equal_input_plus_expression_at_one_zero_eq_four_intensity
#print axioms FresnelWave.equal_input_plus_expression_at_neg_one_zero_eq_zero
#print axioms FresnelWave.plus_expression_neg_one_zero_eq_difference_squares
#print axioms FresnelWave.equal_input_plus_expression_at_zero_pm_one_eq_two_intensity
#print axioms FresnelWave.ab_probability_plus_nonneg
#print axioms FresnelWave.ab_probability_minus_nonneg
#print axioms FresnelWave.asymptotic_truncation_negative_prob_iff
#print axioms sample_brahmagupta_fibonacci_fresnel_int
#print axioms sample_equal_input_and_asymptotic_threshold_int

end InfoGeometry.QuantumContext.AharonovBohmFresnelAudit
