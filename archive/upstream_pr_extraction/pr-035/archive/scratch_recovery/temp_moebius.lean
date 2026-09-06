import InfoGeometry.Algebra.PrimeA1RootSystem
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Factors
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.SplitIfs

namespace InfoGeometry.Arithmetic

open InfoGeometry.Algebra
open ArithmeticFunction

def weylToNat {S : PrimeA1RootSystem} (w : S.WeylGroup) : ℕ :=
  w.prod (fun p => p.val)

theorem weyl_toNat_ne_zero {S : PrimeA1RootSystem} (w : S.WeylGroup) :
    weylToNat w ≠ 0 := by
  dsimp [weylToNat]
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact (S.all_prime p.val p.property).ne_zero

theorem weyl_toNat_squarefree {S : PrimeA1RootSystem} (w : S.WeylGroup) :
    Squarefree (weylToNat w) := by
  apply Nat.squarefree_of_factorization_le_one (weyl_toNat_ne_zero w)
  intro q
  dsimp [weylToNat]
  rw [Nat.factorization_prod_apply]
  · by_cases hq : Nat.Prime q
    · let f := fun (p : {x // x ∈ S.P}) => if p.val = q then (1 : ℕ) else 0
      have h_sum : (Finset.sum w fun p => (p.val).factorization q) = Finset.sum w f := by
        apply Finset.sum_congr rfl
        intro p hp
        have hp_prime := S.all_prime p.val p.property
        dsimp [f]
        split_ifs with h_pq
        · rw [h_pq]
          exact hq.factorization_self
        · rw [Nat.factorization_eq_zero_of_not_dvd]
          · intro h_div
            apply h_pq
            exact ((hp_prime.eq_one_or_self_of_dvd q h_div).resolve_left hq.ne_one).symm
      rw [h_sum]
      rw [Finset.sum_boole]
      have h_unique : (w.filter (fun p => p.val = q)).card ≤ 1 := by
        rw [Finset.card_le_one_iff]
        intro hx hy
        have h1 := (Finset.mem_filter.mp hx).2
        have h2 := (Finset.mem_filter.mp hy).2
        ext
        rw [h1, h2]
      exact h_unique
    · have : ∀ p ∈ w, (p.val).factorization q = 0 := by
        intro p hp
        exact Nat.factorization_eq_zero_of_not_prime _ hq
      simp [this]
  · intro p hp
    exact (S.all_prime p.val p.property).ne_zero

theorem weyl_sign_eq_moebius {S : PrimeA1RootSystem} (w : S.WeylGroup) :
    (PrimeA1RootSystem.signature w : ℤ) = moebius (weylToNat w) := by
  let n := weylToNat w
  have h_sq : Squarefree n := weyl_toNat_squarefree w
  rw [moebius_apply_of_squarefree h_sq]
  rw [PrimeA1RootSystem.signature]
  have h_card : cardFactors n = w.card := by
    dsimp [n, weylToNat]
    rw [Finset.prod_eq_multiset_prod]
    rw [cardFactors_multiset_prod]
    · have : (fun p => cardFactors p.val) = (fun p : {x // x ∈ S.P} => 1) := by
        ext p
        exact cardFactors_apply_prime (S.all_prime p.val p.property)
      simp only [Multiset.map_map, this]
      simp only [Multiset.map_const, Multiset.sum_replicate, smul_eq_mul, mul_one]
      rw [Finset.card_def]
    · exact weyl_toNat_ne_zero w
  rw [h_card]
  -- Instead of Int.neg_one_pow, use direct split
  by_cases h_even : w.card % 2 = 0
  · rw [if_pos h_even]
    -- (-1)^even = 1
    have h_even_real : Even w.card := Nat.even_iff.mpr h_even
    rw [Int.neg_one_pow_eq_one_iff_even.mpr h_even_real]
  · rw [if_neg h_even]
    -- (-1)^odd = -1
    have h_odd : Odd w.card := Nat.odd_iff.mpr (Nat.mod_two_ne_zero.mp h_even)
    rw [Int.neg_one_pow_eq_neg_one_iff_odd.mpr h_odd]

end InfoGeometry.Arithmetic
