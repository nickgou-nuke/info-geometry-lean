import InfoGeometry.Algebra.Zorn.G2FlagOrbitPartitionCertificate
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Algebra.Zorn.G2LeanPCFactorDiscovery

open InfoGeometry.Algebra.Zorn.G2FlagOrbitPartitionCertificate
open InfoGeometry.Algebra.Zorn.G2FlagWordCertificate
open InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup
open InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2
open InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

def pcPairs : Finset (PCWordExp × PCWordExp) := Finset.univ.product Finset.univ

set_option maxRecDepth 100000 in
theorem pairMatches_73_nonempty :
    (pcPairs.filter (fun p =>
      decide (autMatrix (flagRepresentative 73) =
        autMatrix (pcWord p.1 * weylNF (orbitWeyl 1).1 (orbitWeyl 1).2 * pcWord p.2)) = true)).Nonempty := by
  decide

set_option maxRecDepth 100000 in
theorem pairMatches_73_factorization :
    ∃ e₁ e₂ : PCWordExp,
      flagRepresentative 73 =
        pcWord e₁ * weylNF (orbitWeyl 1).1 (orbitWeyl 1).2 * pcWord e₂ := by
  obtain ⟨p, hp⟩ := pairMatches_73_nonempty
  have hp' := (Finset.mem_filter.mp hp).2
  have hmat :
      autMatrix (flagRepresentative 73) =
        autMatrix (pcWord p.1 * weylNF (orbitWeyl 1).1 (orbitWeyl 1).2 * pcWord p.2) :=
    of_decide_eq_true hp'
  exact ⟨p.1, p.2, autMatrix_injective hmat⟩

set_option maxRecDepth 100000 in
theorem pairMatches_178_nonempty :
    (pcPairs.filter (fun p =>
      decide (autMatrix (flagRepresentative 178) =
        autMatrix (pcWord p.1 * weylNF (orbitWeyl 1).1 (orbitWeyl 1).2 * pcWord p.2)) = true)).Nonempty := by
  decide

set_option maxRecDepth 100000 in
theorem pairMatches_178_factorization :
    ∃ e₁ e₂ : PCWordExp,
      flagRepresentative 178 =
        pcWord e₁ * weylNF (orbitWeyl 1).1 (orbitWeyl 1).2 * pcWord e₂ := by
  obtain ⟨p, hp⟩ := pairMatches_178_nonempty
  have hp' := (Finset.mem_filter.mp hp).2
  have hmat :
      autMatrix (flagRepresentative 178) =
        autMatrix (pcWord p.1 * weylNF (orbitWeyl 1).1 (orbitWeyl 1).2 * pcWord p.2) :=
    of_decide_eq_true hp'
  exact ⟨p.1, p.2, autMatrix_injective hmat⟩

end InfoGeometry.Algebra.Zorn.G2LeanPCFactorDiscovery
