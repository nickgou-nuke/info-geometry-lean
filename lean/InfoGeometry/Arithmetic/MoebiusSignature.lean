import InfoGeometry.Algebra.PrimeA1RootSystem
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Nat.Squarefree

/-!
# Möbius Signature Equivalence

Proves the "ParityTraceWitness": the Weyl group signature $\text{sgn}(w)$ 
is exactly the Möbius function $\mu(n)$ for the squarefree product of the 
primes in the cutoff.
-/

namespace InfoGeometry.Arithmetic

open InfoGeometry.Algebra
open scoped ArithmeticFunction.Moebius
open scoped BigOperators

/--
The mapping from a Weyl group element (subset of primes) to a squarefree integer.
$w \mapsto n = \prod_{p \in w} p$.
-/
def weylToNat {S : PrimeA1RootSystem} (w : S.WeylGroup) : ℕ :=
  ∏ p ∈ (w : Finset S.P), (p : ℕ)

/-- The Weyl cutoff product is squarefree. -/
theorem weyl_toNat_squarefree {S : PrimeA1RootSystem} (w : S.WeylGroup) :
    Squarefree (weylToNat w) := by
  unfold weylToNat
  refine Finset.squarefree_prod_of_pairwise_isCoprime ?_ ?_
  · intro x hx y hy hxy
    have hx' : Nat.Prime x := S.all_prime x x.property
    have hy' : Nat.Prime y := S.all_prime y y.property
    simpa [Function.onFun, Nat.coprime_iff_isRelPrime] using
      ((Nat.coprime_primes hx' hy').2 fun hval => hxy (Subtype.ext hval))
  · intro x hx
    exact (S.all_prime x x.property).squarefree

/-- The Weyl signature matches the Möbius sign of the cutoff product. -/
theorem weyl_sign_eq_moebius {S : PrimeA1RootSystem} (w : S.WeylGroup) :
    (S.signature w : ℤ) = μ (weylToNat w) := by
  have hsig : (S.signature w : ℤ) = (-1 : ℤ) ^ w.card := by
    rw [PrimeA1RootSystem.signature]
    simpa [Nat.even_iff] using (neg_one_pow_eq_ite (R := ℤ) (n := w.card)).symm
  have hμ : μ (weylToNat w) = (-1 : ℤ) ^ w.card := by
    unfold weylToNat
    have hmap :
        μ (∏ x ∈ (w : Finset S.P), (x : ℕ)) = ∏ x ∈ (w : Finset S.P), (μ (x : ℕ) : ℤ) := by
      refine ArithmeticFunction.IsMultiplicative.map_prod
        (g := fun x : S.P => (x : ℕ))
        (f := μ) ArithmeticFunction.isMultiplicative_moebius (w : Finset S.P) ?_
      intro x hx y hy hxy
      have hx' : Nat.Prime x := S.all_prime x x.property
      have hy' : Nat.Prime y := S.all_prime y y.property
      exact (Nat.coprime_primes hx' hy').2 fun hval => hxy (Subtype.ext hval)
    rw [hmap]
    have hprime (x : S.P) : (μ (x : ℕ) : ℤ) = -1 := by
      exact ArithmeticFunction.moebius_apply_prime (S.all_prime x x.property)
    have hprod_eq : ∏ x ∈ (w : Finset S.P), (μ (x : ℕ) : ℤ) = ∏ x ∈ (w : Finset S.P), (-1 : ℤ) :=
      Finset.prod_congr rfl (fun x _ => hprime x)
    rw [hprod_eq]
    exact Finset.prod_const (-1 : ℤ)
  exact hsig.trans hμ.symm

end InfoGeometry.Arithmetic
