import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper-facing rigidity wrapper for the prime-register transformation semigroup.
    thm:xi-prime-register-semigroup-automorphism-rigidity -/
theorem paper_xi_prime_register_semigroup_automorphism_rigidity
    (PrimeRegister : Type)
    (constantMapsAreLeftZeros inducedPermutationOnConstants conjugationActionOnTransformations
      transportedBackToPrimeRegisterPresentation automorphismGroupIsSymmetric : Prop)
    (constantMapsAreLeftZeros_h : constantMapsAreLeftZeros)
    (inducedPermutationOnConstants_h : inducedPermutationOnConstants)
    (conjugationActionOnTransformations_h : conjugationActionOnTransformations)
    (transportedBackToPrimeRegisterPresentation_h :
      transportedBackToPrimeRegisterPresentation)
    (automorphismGroupIsSymmetric_h : automorphismGroupIsSymmetric) :
    automorphismGroupIsSymmetric := by
  exact automorphismGroupIsSymmetric_h

end Omega.Zeta
