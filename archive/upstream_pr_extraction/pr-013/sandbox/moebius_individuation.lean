import InfoGeometry.Algebra.PrimeA1RootSystem
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Prime.Basic

/-!
# Sandbox: Moebius Signature Individuation
Proving the identity between Weyl signatures and the Moebius function.
-/

namespace InfoGeometry.Sandbox

open InfoGeometry.Algebra
open scoped ArithmeticFunction.Moebius

/--
The mapping from a Weyl group element (subset of primes) to a squarefree integer.
$w \mapsto n = \prod_{p \in w} p$.
-/
def weylToNat {S : PrimeA1RootSystem} (w : S.WeylGroup) : ℕ :=
  w.prod (fun p => p.val)

/--
PRISTINE CONSTRUCTIVE THEOREM: Weyl to Nat is Squarefree.
-/
theorem weylToNat_squarefree {S : PrimeA1RootSystem} (w : S.WeylGroup) :
    Nat.Squarefree (weylToNat w) := by
  unfold weylToNat
  apply Nat.squarefree_prod_primes
  · intro p hp
    -- Every p in w is a prime from S.P
    exact S.all_prime p p.property
  · -- Every p in w is distinct
    intro p hp q hq hne
    intro heq
    -- p and q are distinct as elements of the Finset subtype
    have heq_val : p.val = q.val := heq
    -- But heq_val implies p = q since they are subtypes of the same set
    have hpq : p = q := Subtype.ext heq_val
    exact hne hpq

/-- 
PRISTINE CONSTRUCTIVE THEOREM: Signature as Moebius.
-/
theorem weyl_sign_eq_moebius {S : PrimeA1RootSystem} (w : S.WeylGroup) :
    (S.signature w : ℤ) = μ (weylToNat w) := by
  -- 1. Get squarefree property
  have h_sqfree := weylToNat_squarefree (S := S) w
  
  -- 2. μ(n) = (-1)^ω(n) for squarefree n
  rw [ArithmeticFunction.moebius_apply_of_squarefree h_sqfree]
  
  -- 3. cardFactors(prod p_i) = number of primes
  have h_card : Nat.cardFactors (weylToNat w) = w.card := by
    unfold weylToNat
    rw [Nat.cardFactors_prod]
    · simp
    · intro p hp
      exact (S.all_prime p p.property).ne_zero

  rw [h_card]
  
  -- 4. Match (-1)^w.card with the signature definition
  unfold PrimeA1RootSystem.signature
  split
  · -- Case card is even
    have h_even : w.card % 2 = 0 := by assumption
    rw [Int.neg_one_pow_eq_one_iff_even.mpr h_even]
    rfl
  · -- Case card is odd
    have h_odd : w.card % 2 ≠ 0 := by assumption
    have h_not_even : ¬ (w.card % 2 = 0) := h_odd
    rw [Int.neg_one_pow_eq_neg_one_iff_odd.mpr]
    · rfl
    · rw [Nat.odd_iff_not_even]
      exact h_not_even

end InfoGeometry.Sandbox
