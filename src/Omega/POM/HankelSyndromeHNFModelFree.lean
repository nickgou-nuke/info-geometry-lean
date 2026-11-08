import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Tactic
import Omega.POM.HankelSyndromeHNFUnique

namespace Omega.POM

/-- Concrete model-free HNF consequence: the canonical tail basis is the unique
linearly independent spanning family in the truncated-multiple model. -/
theorem paper_pom_hankel_syndrome_hnf_model_free (n d : ℕ) (hd : d ≤ n) :
    ∃! B : Fin (n - d) → pom_hankel_syndrome_module_rank_and_generators_module n d,
      B = pom_hankel_syndrome_module_rank_and_generators_generators n d hd ∧
      LinearIndependent ℤ B ∧
      Submodule.span ℤ (Set.range B) = ⊤ := by
  exact paper_pom_hankel_syndrome_hnf_unique n d hd

end Omega.POM
