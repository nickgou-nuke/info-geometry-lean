import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Nat.Squarefree
import InfoGeometry.Arithmetic.PrimeBitFiniteMertens
import InfoGeometry.Arithmetic.PrimonWittenIndexZetaBridge

noncomputable section

open scoped BigOperators
open scoped ArithmeticFunction.Moebius

namespace InfoGeometry.Arithmetic.PrimeBitFiniteMobiusPolynomial

open InfoGeometry.Arithmetic
open InfoGeometry.Arithmetic.ChiralPrimonGas
open InfoGeometry.Arithmetic.PrimeBitFiniteMertens
open InfoGeometry.Arithmetic.PrimeBitMobiusParityBridge
open InfoGeometry.Arithmetic.MobiusMertensRHEquivalence
open InfoGeometry.Arithmetic.PrimonWittenIndexZetaBridge

def primeCutoffLattice (B : ℕ) : PrimeBitLattice :=
  ⟨(primeCutoffRegister B).primes, (primeCutoffRegister B).prime_mem⟩

def integerCutoffMobiusPolynomial (B : ℕ) (x : ℕ → ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 B, (ArithmeticFunction.moebius n : ℂ) * x n

def primeCutoffMobiusPolynomial (B : ℕ) (x : ℕ → ℂ) : ℂ :=
  ∑ ε ∈ S_B (primeCutoffLattice B) B,
    ((-1 : ℤ) ^ ε.1.card : ℂ) * x (primeBitInteger (primeCutoffLattice B) ε)

theorem primeCutoffMobiusPolynomial_eq_integerCutoffSquarefree
    (B : ℕ) (x : ℕ → ℂ) :
    primeCutoffMobiusPolynomial B x =
      ∑ n ∈ integerCutoffSquarefree B,
        (ArithmeticFunction.moebius n : ℂ) * x n := by
  classical
  unfold primeCutoffMobiusPolynomial
  refine Finset.sum_bij (fun ε _ => primeBitInteger (primeCutoffLattice B) ε)
    ?_ ?_ ?_ ?_
  · intro ε hε
    have hε' : ε ∈
        ((primeCutoffLattice B).primes.powerset.attach.map
          { toFun := fun S =>
              (⟨S.1, Finset.mem_powerset.mp S.2⟩ :
                PrimeBitState (primeCutoffLattice B))
            inj' := by
              intro S T hST
              exact Subtype.ext
                (congrArg (fun U : PrimeBitState (primeCutoffLattice B) => U.1) hST) }).filter
          (fun ε => primeBitInteger (primeCutoffLattice B) ε ≤ B) := by
      simpa [S_B] using hε
    rw [Finset.mem_filter] at hε'
    change primeBitInteger (primeCutoffLattice B) ε ∈
      (Finset.Icc 1 B).filter Squarefree
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_Icc.mpr
      ⟨Nat.one_le_iff_ne_zero.mpr (primeBitInteger_ne_zero ε), hε'.2⟩,
      primeBitInteger_squarefree ε⟩
  · intro ε₁ hε₁ ε₂ hε₂ heq
    change primeBitInteger (primeCutoffLattice B) ε₁ =
      primeBitInteger (primeCutoffLattice B) ε₂ at heq
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
    have hsub : εval ⊆ (primeCutoffLattice B).primes := by
      intro p hp
      have hpmem := Nat.mem_primeFactors.mp hp
      exact (mem_primesUpto_iff).2
        ⟨(Nat.le_of_dvd hnpos hpmem.2.1).trans hIcc.2, hpmem.1⟩
    let ε : PrimeBitState (primeCutoffLattice B) := ⟨εval, hsub⟩
    have hεmem : ε ∈ S_B (primeCutoffLattice B) B := by
      change ε ∈
        ((primeCutoffLattice B).primes.powerset.attach.map
          { toFun := fun S =>
              (⟨S.1, Finset.mem_powerset.mp S.2⟩ :
                PrimeBitState (primeCutoffLattice B))
            inj' := by
              intro S T hST
              exact Subtype.ext
                (congrArg (fun U : PrimeBitState (primeCutoffLattice B) => U.1) hST) }).filter
          (fun ε => primeBitInteger (primeCutoffLattice B) ε ≤ B)
      rw [Finset.mem_filter]
      refine ⟨?_, ?_⟩
      · rw [Finset.mem_map]
        let S : {S : Finset ℕ // S ∈ (primeCutoffLattice B).primes.powerset} :=
          ⟨εval, Finset.mem_powerset.mpr hsub⟩
        refine ⟨S, Finset.mem_attach _ S, ?_⟩
        rfl
      · change ∏ p ∈ εval, p ≤ B
        rw [show εval = n.primeFactors from rfl,
          Nat.prod_primeFactors_of_squarefree hsq]
        exact hIcc.2
    refine ⟨ε, hεmem, ?_⟩
    change ∏ p ∈ εval, p = n
    exact Nat.prod_primeFactors_of_squarefree hsq
  · intro ε hε
    change ((-1 : ℤ) ^ ε.1.card : ℂ) *
        x (primeBitInteger (primeCutoffLattice B) ε) =
      (ArithmeticFunction.moebius (primeBitInteger (primeCutoffLattice B) ε) : ℂ) *
        x (primeBitInteger (primeCutoffLattice B) ε)
    rw [mobius_primeBitInteger_eq_parity]
    norm_num

theorem primeCutoffMobiusPolynomial_eq_integerCutoff
    (B : ℕ) (x : ℕ → ℂ) :
    primeCutoffMobiusPolynomial B x =
      integerCutoffMobiusPolynomial B x := by
  classical
  rw [primeCutoffMobiusPolynomial_eq_integerCutoffSquarefree]
  unfold integerCutoffMobiusPolynomial integerCutoffSquarefree
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl ?_
  intro n hn
  by_cases h : Squarefree n
  · simp [h]
  · simp [h, ArithmeticFunction.moebius_eq_zero_of_not_squarefree h]

theorem primeCutoffMobiusPolynomial_one_eq_mertensFunction (B : ℕ) :
    primeCutoffMobiusPolynomial B (fun _ => 1) =
      (mertensFunction B : ℂ) := by
  rw [primeCutoffMobiusPolynomial_eq_integerCutoff B (fun _ => 1)]
  simp only [integerCutoffMobiusPolynomial, mul_one]
  unfold mertensFunction
  norm_cast
  have hzero : ArithmeticFunction.moebius 0 = 0 := rfl
  have herase := Finset.sum_erase (Finset.range (B + 1)) hzero
  have hset : (Finset.range (B + 1)).erase 0 = Finset.Icc 1 B := by
    ext n
    simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_Icc,
      Nat.lt_succ_iff]
    omega
  rw [← hset, ← herase]

theorem primeCutoffMobiusPolynomial_boltzmann_eq_wittenIndexSum
    (B : ℕ) (β : ℝ) :
    primeCutoffMobiusPolynomial B
        (fun n => (boltzmannWeight β n : ℂ)) =
      ∑ n ∈ Finset.Icc 1 B, (wittenIndexTerm β n : ℂ) := by
  rw [primeCutoffMobiusPolynomial_eq_integerCutoff]
  unfold integerCutoffMobiusPolynomial wittenIndexTerm
  push_cast
  rfl

end InfoGeometry.Arithmetic.PrimeBitFiniteMobiusPolynomial
