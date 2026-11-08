import Mathlib.Tactic
import Omega.Conclusion.SingularRingFaithfulSemigroup

namespace Omega.Conclusion

theorem paper_conclusion_singular_ring_prime_composition_irreducibility
    (D : Omega.Conclusion.SingularRingFaithfulSemigroupData) (n : ℕ) (hn : 2 ≤ n) :
    Nat.Prime n ↔
      ¬ ∃ a b : ℕ, 2 ≤ a ∧ 2 ≤ b ∧
        Function.comp (D.rationalMap a) (D.rationalMap b) = D.rationalMap n := by
  rcases paper_conclusion_singular_ring_faithful_semigroup D with ⟨hsemigroup, hfaithful⟩
  constructor
  · intro hprime hdecomp
    rcases hdecomp with ⟨a, b, ha, hb, hcomp⟩
    have hab_eq : a * b = n := by
      have hmaps : D.rationalMap (a * b) = D.rationalMap n := by
        exact (hsemigroup a b (by omega) (by omega)).symm.trans hcomp
      exact (hfaithful (a * b) n hmaps).2
    exact (Nat.not_prime_of_mul_eq hab_eq (by omega) (by omega)) hprime
  · intro hindecomp
    rw [Nat.prime_def_lt']
    refine ⟨hn, ?_⟩
    intro a ha hlt hdiv
    rcases hdiv with ⟨b, rfl⟩
    have hb : 2 ≤ b := by
      rcases b with _ | _ | b
      · simp at hlt
      · simp at hlt
      · omega
    exact hindecomp ⟨a, b, ha, hb, hsemigroup a b (by omega) (by omega)⟩

end Omega.Conclusion
