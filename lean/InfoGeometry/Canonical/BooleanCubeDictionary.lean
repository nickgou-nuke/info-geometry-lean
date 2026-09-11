import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.FormalPrimeRootSystem
import InfoGeometry.Arithmetic.PrimeBitWittenIndex
import InfoGeometry.Arithmetic.PrimeCantorLatticeDirac
import InfoGeometry.Canonical.ParityTraceWitness

open scoped BigOperators
open InfoGeometry.Canonical.FormalPrimeRootSystem
open InfoGeometry.Arithmetic.PrimeBitWittenIndex
open InfoGeometry.Arithmetic.PrimeCantorLatticeDirac
open InfoGeometry.Canonical.ParityTraceWitness

/-!
# InfoGeometry.Canonical.BooleanCubeDictionary

Functorial dictionary among the multiple presentations of the finite Boolean cube.

Following the emergent structural paradigm (TOSP), this module formalizes the
bridges between the three primary presentations of the information-geometric
reality for a finite prime cutoff P:

1.  **Subsets:** `Finset ℕ` where `S ⊆ P.primes` (The combinatorial L0/L1 layer).
2.  **Integers:** `ℕ` square-free products (The arithmetic L2 layer).
3.  **States:** `PrimeBitState P` occupancy words (The functional L4 layer).

The bridges are established via explicit `Equiv` intertwiners and
preservation 2-morphisms.
-/

namespace InfoGeometry.Canonical.BooleanCubeDictionary

variable (P : PrimeRegister)

/-! ## 1. Subset <-> State word bridge -/

/--
Equivalence between explicit Bool-state words and subsets of the register.
-/
@[rep_depth thermo]
def stateToSubsetEquiv : PrimeBitState P ≃ {S : Finset ℕ // S ⊆ P.primes} where
  toFun ψ := ⟨occupiedPrimeSet P ψ, occupiedPrimeSet_subset P ψ⟩
  invFun S := fun p => p.val ∈ S.val
  left_inv ψ := by
    ext p
    simp [occupiedPrimeSet]
  right_inv S := by
    apply Subtype.ext
    ext x
    simp [occupiedPrimeSet]
    intro h
    exact S.property h

/-! ## 2. Subset <-> Arithmetic bridge -/

/--
The set of square-free integers whose prime factors are all contained in P.
-/
@[rep_depth thermo]
def ArithmeticRegister (P : PrimeRegister) :=
  {n : ℕ // Squarefree n ∧ ∀ p, p.Prime → p ∣ n → p ∈ P.primes}

/--
Equivalence between prime subsets and their square-free products.
-/
@[rep_depth thermo]
def subsetToArithmeticEquiv : {S : Finset ℕ // S ⊆ P.primes} ≃ ArithmeticRegister P where
  toFun S := ⟨∏ p ∈ S.val, p, by
    constructor
    · refine Finset.squarefree_prod_of_pairwise_isCoprime ?_ ?_
      · intro x hx y hy hxy
        have hx_prime : Nat.Prime x := P.prime_mem x (S.property hx)
        have hy_prime : Nat.Prime y := P.prime_mem y (S.property hy)
        simpa [Function.onFun, Nat.coprime_iff_isRelPrime] using
          ((Nat.coprime_primes hx_prime hy_prime).2 hxy)
      · intro x hx
        exact (P.prime_mem x (S.property hx)).squarefree
    · intro p hp hdiv
      have hp_prime : Nat.Prime p := hp
      rw [hp_prime.prime.dvd_finset_prod_iff] at hdiv
      rcases hdiv with ⟨a, ha, hpa⟩
      have ha_prime : a.Prime := P.prime_mem a (S.property ha)
      have heq : a = p := (Nat.Prime.dvd_iff_eq ha_prime hp_prime.ne_one).mp hpa
      subst heq
      exact S.property ha
  ⟩
  invFun n := ⟨n.val.primeFactorsList.toFinset, by
    intro p hp
    have hp_mem : p ∈ n.val.primeFactorsList := List.mem_toFinset.mp hp
    have hprime := Nat.prime_of_mem_primeFactorsList hp_mem
    exact n.property.2 p hprime (Nat.dvd_of_mem_primeFactorsList hp_mem)
  ⟩
  left_inv S := by
    apply Subtype.ext
    ext p
    constructor
    · intro hp
      rw [List.mem_toFinset] at hp
      have hne : ∏ x ∈ S.val, x ≠ 0 := by
        apply Finset.prod_ne_zero_iff.mpr
        intro x hx
        exact (P.prime_mem x (S.property hx)).ne_zero
      rw [Nat.mem_primeFactorsList hne] at hp
      have hprime : p.Prime := hp.1
      have hdvd : p ∣ ∏ x ∈ S.val, x := hp.2
      rw [hprime.prime.dvd_finset_prod_iff] at hdvd
      rcases hdvd with ⟨a, ha, hpa⟩
      have ha_prime : a.Prime := P.prime_mem a (S.property ha)
      have heq : a = p := (Nat.Prime.dvd_iff_eq ha_prime hprime.ne_one).mp hpa
      subst heq
      exact ha
    · intro hp
      rw [List.mem_toFinset]
      have hne : ∏ x ∈ S.val, x ≠ 0 := by
        apply Finset.prod_ne_zero_iff.mpr
        intro x hx
        exact (P.prime_mem x (S.property hx)).ne_zero
      rw [Nat.mem_primeFactorsList hne]
      have hprime : p.Prime := P.prime_mem p (S.property hp)
      constructor
      · exact hprime
      · exact Finset.dvd_prod_of_mem (fun x => x) hp
  right_inv n := by
    apply Subtype.ext
    simp
    exact Nat.prod_primeFactors_of_squarefree n.property.1

/-! ## 3. Preservation 2-morphisms -/

/--
The intertwiner preserves the Weyl-Möbius sign character.
-/
@[rep_depth thermo]
theorem sign_preservation (S : {S : Finset ℕ // S ⊆ P.primes}) :
    (subsetWeylSign S.val : ℤ) =
      ArithmeticFunction.moebius (subsetToArithmeticEquiv P S).val := by
  have hS := S.property
  have hprime : ∀ p ∈ S.val, p.Prime := fun p hp => P.prime_mem p (hS hp)
  rw [subsetWeylSign, subsetToArithmeticEquiv]
  simp
  exact (mobius_prime_product_eq_parity S.val hprime).symm

/--
The dictionary is coherent: all three presentations agree on the truth of the
Boolean cube structure.
-/
@[rep_depth thermo]
def fullDictionaryEquiv : PrimeBitState P ≃ ArithmeticRegister P :=
  (stateToSubsetEquiv P).trans (subsetToArithmeticEquiv P)

end InfoGeometry.Canonical.BooleanCubeDictionary
