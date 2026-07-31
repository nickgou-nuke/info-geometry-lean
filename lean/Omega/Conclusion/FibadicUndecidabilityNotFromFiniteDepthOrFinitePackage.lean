import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
import Omega.Conclusion.FibadicOpenIdealFiniteQuotientClassification

namespace Omega.Conclusion

/-- The finite-valued fibadic observable carried by this finite package: a positive conductor and
a value in its cyclic finite quotient. -/
abbrev conclusion_fibadic_undecidability_not_from_finite_depth_or_finite_package_observable :
    Type :=
  Σ I : conclusion_fibadic_open_ideal_finite_quotient_classification_open_ideal,
    conclusion_fibadic_open_ideal_finite_quotient_classification_finite_quotient I

/-- Paper label:
`cor:conclusion-fibadic-undecidability-not-from-finite-depth-or-finite-package`. -/
theorem paper_conclusion_fibadic_undecidability_not_from_finite_depth_or_finite_package
    (conductorBound : ℕ) (primePackage : Finset ℕ) :
    Nonempty (Decidable (∀ p ∈ primePackage, p ∣ conductorBound)) ∧
      (conclusion_fibadic_open_ideal_finite_quotient_classification_statement ∧
        ¬ ((∀ p ∈ primePackage, p ∣ conductorBound) ∧
          ¬ Nonempty (Decidable (∀ p ∈ primePackage, p ∣ conductorBound)))) := by
  classical
  have hdec : Nonempty (Decidable (∀ p ∈ primePackage, p ∣ conductorBound)) :=
    ⟨inferInstance⟩
  refine ⟨hdec, ?_⟩
  refine ⟨paper_conclusion_fibadic_open_ideal_finite_quotient_classification, ?_⟩
  intro hbad
  exact hbad.2 hdec

end Omega.Conclusion
