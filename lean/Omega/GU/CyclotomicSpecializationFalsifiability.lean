import Omega.GU.CyclotomicGcdStability

namespace Omega.GU

universe u

/-- Exceptional cyclotomic layers form a finite witness set under residual gcd triviality. -/
theorem paper_gut_cyclotomic_specialization_falsifiability
    (BivariatePolynomial : Type u)
    (nontrivialCommonFactor : BivariatePolynomial → Prop)
    (infinitelyManyCommonSlowModes residualGcdTrivial extraGcdAtInfinitelyManyLevels : Prop)
    (Layer : Type u) [DecidableEq Layer]
    (exceptionalLayer : Layer → Prop)
    (specializationRigidity :
      infinitelyManyCommonSlowModes → ∃ H : BivariatePolynomial, nontrivialCommonFactor H)
    (extraGcdForcesInfinitelyManyCommonSlowModes :
      extraGcdAtInfinitelyManyLevels → infinitelyManyCommonSlowModes)
    (residualGcdExcludesNontrivialCommonFactor :
      residualGcdTrivial → ¬ ∃ H : BivariatePolynomial, nontrivialCommonFactor H)
    (exceptionalLayersForceExtraGcdAtInfinitelyManyLevels :
      Set.Infinite {ℓ : Layer | exceptionalLayer ℓ} → extraGcdAtInfinitelyManyLevels) :
    residualGcdTrivial →
      ∃ witnessSet : Finset Layer, ∀ ℓ, exceptionalLayer ℓ → ℓ ∈ witnessSet := by
  intro hResidual
  have hnotInfinite : ¬ Set.Infinite {ℓ : Layer | exceptionalLayer ℓ} := by
    intro hInfinite
    exact (paper_gut_cyclotomic_gcd_stability BivariatePolynomial
      nontrivialCommonFactor infinitelyManyCommonSlowModes residualGcdTrivial
      extraGcdAtInfinitelyManyLevels specializationRigidity
      extraGcdForcesInfinitelyManyCommonSlowModes residualGcdExcludesNontrivialCommonFactor
      hResidual)
      (exceptionalLayersForceExtraGcdAtInfinitelyManyLevels hInfinite)
  have hfinite : Set.Finite {ℓ : Layer | exceptionalLayer ℓ} := Set.not_infinite.mp hnotInfinite
  refine ⟨hfinite.toFinset, ?_⟩
  intro ℓ hℓ
  exact hfinite.mem_toFinset.mpr hℓ

/-- Chapter-facing theorem for finite falsifiability of cyclotomic specializations. -/
theorem paper_cyclotomic_specialization_falsifiability
    (BivariatePolynomial : Type u)
    (nontrivialCommonFactor : BivariatePolynomial → Prop)
    (infinitelyManyCommonSlowModes residualGcdTrivial extraGcdAtInfinitelyManyLevels : Prop)
    (Layer : Type u) [DecidableEq Layer]
    (exceptionalLayer : Layer → Prop)
    (specializationRigidity :
      infinitelyManyCommonSlowModes → ∃ H : BivariatePolynomial, nontrivialCommonFactor H)
    (extraGcdForcesInfinitelyManyCommonSlowModes :
      extraGcdAtInfinitelyManyLevels → infinitelyManyCommonSlowModes)
    (residualGcdExcludesNontrivialCommonFactor :
      residualGcdTrivial → ¬ ∃ H : BivariatePolynomial, nontrivialCommonFactor H)
    (exceptionalLayersForceExtraGcdAtInfinitelyManyLevels :
      Set.Infinite {ℓ : Layer | exceptionalLayer ℓ} → extraGcdAtInfinitelyManyLevels) :
    residualGcdTrivial →
      ∃ witnessSet : Finset Layer, ∀ ℓ, exceptionalLayer ℓ → ℓ ∈ witnessSet := by
  exact paper_gut_cyclotomic_specialization_falsifiability BivariatePolynomial
    nontrivialCommonFactor infinitelyManyCommonSlowModes residualGcdTrivial
    extraGcdAtInfinitelyManyLevels Layer exceptionalLayer specializationRigidity
    extraGcdForcesInfinitelyManyCommonSlowModes residualGcdExcludesNontrivialCommonFactor
    exceptionalLayersForceExtraGcdAtInfinitelyManyLevels

end Omega.GU
