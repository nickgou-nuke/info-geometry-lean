import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Nat.Squarefree
import InfoGeometry.Arithmetic.PrimeBitLattice
import InfoGeometry.Arithmetic.PrimeBitMobiusParityBridge
import InfoGeometry.Arithmetic.MobiusMertensRHEquivalence
import InfoGeometry.Arithmetic.ChiralPrimonGas

noncomputable section

open Nat
open Finset
open ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace InfoGeometry.Arithmetic.PrimeBitFiniteMertens

open InfoGeometry.Arithmetic
open InfoGeometry.Arithmetic.MobiusMertensRHEquivalence
open InfoGeometry.Arithmetic.PrimeBitMobiusParityBridge
open InfoGeometry.Arithmetic.ChiralPrimonGas

def integerCutoffSquarefree (B : ℕ) : Finset ℕ :=
  (Finset.Icc 1 B).filter Squarefree

def S_B (L : PrimeBitLattice) (B : ℕ) : Finset (PrimeBitState L) :=
  (L.primes.powerset.attach.map
      { toFun := fun S =>
          (⟨S.1, Finset.mem_powerset.mp S.2⟩ : PrimeBitState L)
        inj' := by
          intro S T hST
          exact Subtype.ext (congrArg (fun U : PrimeBitState L => U.1) hST) }).filter
    (fun ε => primeBitInteger L ε ≤ B)

theorem sum_parity_eq_squarefree_mobius_sum
    (L : PrimeBitLattice) (B : ℕ)
    (hL : ∀ p ≤ B, Nat.Prime p → p ∈ L.primes) :
    ∑ ε ∈ S_B L B, (-1 : ℤ) ^ ε.1.card =
      ∑ n ∈ integerCutoffSquarefree B,
        ArithmeticFunction.moebius n := by
  classical
  refine Finset.sum_bij (fun ε _ => primeBitInteger L ε) ?_ ?_ ?_ ?_
  · intro ε hε
    have hε' : ε ∈
        (L.primes.powerset.attach.map
          { toFun := fun S =>
              (⟨S.1, Finset.mem_powerset.mp S.2⟩ : PrimeBitState L)
            inj' := by
              intro S T hST
              exact Subtype.ext
                (congrArg (fun U : PrimeBitState L => U.1) hST) }).filter
          (fun ε => primeBitInteger L ε ≤ B) := by
      simpa [S_B] using hε
    rw [Finset.mem_filter] at hε'
    change primeBitInteger L ε ∈ (Finset.Icc 1 B).filter Squarefree
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_Icc.mpr
      ⟨Nat.one_le_iff_ne_zero.mpr (primeBitInteger_ne_zero ε), hε'.2⟩,
      primeBitInteger_squarefree ε⟩
  · intro ε₁ hε₁ ε₂ hε₂ heq
    change primeBitInteger L ε₁ = primeBitInteger L ε₂ at heq
    have h₁ := primeBitInteger_primeFactors ε₁
    have h₂ := primeBitInteger_primeFactors ε₂
    have hsets : ε₁.1 = ε₂.1 := by
      rw [← h₁, heq, h₂]
    exact Subtype.ext hsets
  · intro n hn
    have hn' : n ∈ (Finset.Icc 1 B).filter Squarefree := by
      simpa [integerCutoffSquarefree] using hn
    rw [Finset.mem_filter] at hn'
    have hIcc : 1 ≤ n ∧ n ≤ B := Finset.mem_Icc.mp hn'.1
    have hnpos : 0 < n := hIcc.1
    have hsq : Squarefree n := hn'.2
    let εval : Finset ℕ := n.primeFactors
    have hsub : εval ⊆ L.primes := by
      intro p hp
      have hpmem := (Nat.mem_primeFactors.mp hp)
      exact hL p ((Nat.le_of_dvd hnpos hpmem.2.1).trans hIcc.2) hpmem.1
    let ε : PrimeBitState L := ⟨εval, hsub⟩
    have hεmem : ε ∈ S_B L B := by
      change ε ∈
        (L.primes.powerset.attach.map
          { toFun := fun S =>
              (⟨S.1, Finset.mem_powerset.mp S.2⟩ : PrimeBitState L)
            inj' := by
              intro S T hST
              exact Subtype.ext
                (congrArg (fun U : PrimeBitState L => U.1) hST) }).filter
          (fun ε => primeBitInteger L ε ≤ B)
      rw [Finset.mem_filter]
      refine ⟨?_, ?_⟩
      · rw [Finset.mem_map]
        let S : {S : Finset ℕ // S ∈ L.primes.powerset} :=
          ⟨εval, Finset.mem_powerset.mpr hsub⟩
        refine ⟨S, Finset.mem_attach L.primes.powerset S, ?_⟩
        rfl
      · change ∏ p ∈ εval, p ≤ B
        rw [show εval = n.primeFactors from rfl,
          Nat.prod_primeFactors_of_squarefree hsq]
        exact hIcc.2
    refine ⟨ε, hεmem, ?_⟩
    change ∏ p ∈ εval, p = n
    exact Nat.prod_primeFactors_of_squarefree hsq
  · intro ε hε
    exact (mobius_primeBitInteger_eq_parity ε).symm

theorem sum_parity_eq_mertensFunction
    (L : PrimeBitLattice) (B : ℕ)
    (hL : ∀ p ≤ B, Nat.Prime p → p ∈ L.primes) :
    ∑ ε ∈ S_B L B, (-1 : ℤ) ^ ε.1.card =
      mertensFunction B := by
  have hsq := sum_parity_eq_squarefree_mobius_sum L B hL
  rw [hsq]
  unfold mertensFunction integerCutoffSquarefree
  have hfilter :
      (∑ n ∈ (Finset.Icc 1 B).filter Squarefree,
        ArithmeticFunction.moebius n) =
        ∑ n ∈ Finset.Icc 1 B, ArithmeticFunction.moebius n := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl ?_
    intro n hn
    by_cases h : Squarefree n
    · simp [h]
    · simp [h, ArithmeticFunction.moebius_eq_zero_of_not_squarefree h]
  rw [hfilter]
  have hzero : ArithmeticFunction.moebius 0 = 0 := rfl
  have herase := Finset.sum_erase (Finset.range (B + 1)) hzero
  have hset : (Finset.range (B + 1)).erase 0 = Finset.Icc 1 B := by
    ext n
    simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_Icc,
      Nat.lt_succ_iff]
    omega
  rw [← hset, ← herase]

theorem primeCutoff_sum_parity_eq_mertensFunction (B : ℕ) :
    ∑ ε ∈ S_B (⟨(primeCutoffRegister B).primes,
      (primeCutoffRegister B).prime_mem⟩ : PrimeBitLattice) B,
      (-1 : ℤ) ^ ε.1.card =
      mertensFunction B := by
  apply sum_parity_eq_mertensFunction
    (⟨(primeCutoffRegister B).primes,
      (primeCutoffRegister B).prime_mem⟩ : PrimeBitLattice) B
  intro p hp hpprime
  exact (mem_primesUpto_iff).2 ⟨hp, hpprime⟩

end InfoGeometry.Arithmetic.PrimeBitFiniteMertens
