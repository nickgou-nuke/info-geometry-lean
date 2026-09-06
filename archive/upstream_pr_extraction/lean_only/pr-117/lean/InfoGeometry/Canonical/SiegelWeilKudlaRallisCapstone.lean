/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Automorphic.SiegelWeilKudlaRallisBridge

namespace InfoGeometry.Canonical

open InfoGeometry.Automorphic.SiegelWeilKudlaRallisBridge

/-- Canonical projection capstone for rational special values λ(f)/⟨f,f⟩ ∈ ℚ from the Siegel-Weil-Kudla-Rallis doubling method. -/
theorem siegel_weil_kudla_rallis_rational_special_values_canonical_capstone
    (Cusp : Type*)
    (c : ℚ)
    (inner : Cusp → ℂ)
    (h_inner : ∀ f : Cusp, inner f ≠ 0) :
    let R := NormalizedSpecialValueRationalityWitness.ofRationalFactor Cusp c inner h_inner
    -- 1. Calibration identity: normalizedSpecialValue f = λ(f) / ⟨f,f⟩
    (∀ f : Cusp, R.normalizedSpecialValue f = R.lambda f / R.selfInner f) ∧
    -- 2. Special value rationality: λ(f) / ⟨f,f⟩ ∈ ℚ
    (∀ f : Cusp, ∃ q : ℚ, R.lambda f / R.selfInner f = (q : ℂ)) ∧
    -- 3. Explicit rational value evaluation: λ(f) / ⟨f,f⟩ = (c : ℂ)
    (∀ f : Cusp, R.lambda f / R.selfInner f = (c : ℂ)) := by
  intro R
  refine ⟨
    fun f => R.normalizedSpecialValue_eq f,
    fun f => R.lambda_div_selfInner_is_rational f,
    fun f => by
      dsimp [R, NormalizedSpecialValueRationalityWitness.ofRationalFactor]
      simp [mul_div_cancel_right₀ (c : ℂ) (h_inner f)]
  ⟩

end InfoGeometry.Canonical
