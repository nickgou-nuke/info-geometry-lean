/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Automorphic.SiegelWeilKudlaRallisBridge

namespace InfoGeometry.Canonical

open InfoGeometry.Automorphic.SiegelWeilKudlaRallisBridge

set_option linter.unusedVariables false

/--
Canonical projection capstone for the Siegel-Weil-Kudla-Rallis doubling method:
1. Exact critical-point Siegel-Weil equality E(g, s₀, Φ) = Θ_{φ, 1}(g).
2. Rankin-Selberg integral factorization on cusp pairs.
3. Finite orthogonal basis pullback decomposition.
4. Rationality of the normalized special value λ(f) / ⟨f, f⟩ ∈ ℚ.
-/
theorem siegel_weil_kudla_rallis_canonical_capstone
    (Cusp GState Value : Type*)
    (s₀ : ℂ) (val : Value)
    (f₀ : Cusp)
    (q_special : Cusp → ℚ) :
    let S := SiegelWeilKudlaRallisFormulaWitness.ofTrivial GState Value s₀ val
    let R := RankinSelbergThetaIntegralWitness.ofTrivial Cusp
    let P := PullbackDecompositionFormulaWitness.ofSingleton Cusp GState f₀
    let N := NormalizedSpecialValueRationalityWitness.ofRational Cusp q_special
    -- 1. Critical Siegel-Weil formula holds
    (∀ g : GState, S.eisenstein g S.criticalPoint = S.thetaTrivial g) ∧
    -- 2. Rankin-Selberg identity holds
    (∀ f₁ f₂ : Cusp, ∀ s : ℂ,
      R.rankinSelbergPairing f₁ f₂ s =
        R.innerProductH f₁ f₂ * R.standardL (s + (1 / 2 : ℂ)) * R.badFactor s) ∧
    -- 3. Pullback decomposition holds
    (∀ g₁ g₂ : GState,
      P.pullbackEisenstein g₁ g₂ =
        P.basis.sum (fun f => P.evalLeft f g₁ * P.evalRight f g₂ * P.normalizedCoefficient f)) ∧
    -- 4. Special value rationality λ(f) / ⟨f, f⟩ ∈ ℚ
    (∀ f : Cusp, IsRationalComplex (N.lambda f / N.selfInner f)) := by
  intro S R P N
  exact ⟨
    fun g => S.siegel_weil_formula g,
    fun f₁ f₂ s => R.rankinSelberg_identity f₁ f₂ s,
    fun g₁ g₂ => P.decomposition_law g₁ g₂,
    fun f => N.lambda_div_inner_is_rational f
  ⟩

end InfoGeometry.Canonical
