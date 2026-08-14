import InfoGeometry.Arithmetic.PrimitiveBinarySuperZetaBridge

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Arithmetic.PrimeFermionSupertraceFinite

open InfoGeometry.Arithmetic.PrimitiveBinarySuperZetaBridge

namespace FinitePrimeBitLattice

variable (P : PrimitiveBinarySuperZetaBridge.FinitePrimeBitLattice)

def localPrimeWeight
    (β : ℝ)
    (i : P.Index) : ℝ :=
  Real.exp (-β * Real.log (P.prime i : ℝ))

lemma localPrimeWeight_pos (β : ℝ) (i : P.Index) :
    0 < localPrimeWeight P β i := by
  unfold localPrimeWeight
  exact Real.exp_pos _

def fermionSign
    (ε : P.Profile) : ℝ :=
  ∏ i : P.Index, if ε i then (-1 : ℝ) else 1

def fermionicPartition
    (β : ℝ) : ℝ :=
  ∑ ε : P.Profile, Real.exp (-β * P.bitEnergy ε)

def fermionicSupertrace
    (β : ℝ) : ℝ :=
  ∑ ε : P.Profile, fermionSign P ε * Real.exp (-β * P.bitEnergy ε)

theorem exp_neg_mul_bitEnergy_eq_profile_product
    (β : ℝ)
    (ε : P.Profile) :
    Real.exp (-β * P.bitEnergy ε) =
      ∏ i : P.Index, if ε i then localPrimeWeight P β i else 1 := by
  unfold PrimitiveBinarySuperZetaBridge.FinitePrimeBitLattice.bitEnergy localPrimeWeight
  rw [show -β * (∑ i : P.Index, if ε i then Real.log (P.prime i : ℝ) else 0) =
      ∑ i : P.Index, (-β) * (if ε i then Real.log (P.prime i : ℝ) else 0) by
    rw [Finset.mul_sum]]
  rw [Real.exp_sum]
  refine Finset.prod_congr rfl ?_
  intro i _hi
  by_cases h : ε i <;> simp [h]

theorem fermionicPartition_eq_product
    (β : ℝ) :
    fermionicPartition P β =
      ∏ i : P.Index, (1 + localPrimeWeight P β i) := by
  classical
  unfold fermionicPartition
  simp_rw [exp_neg_mul_bitEnergy_eq_profile_product P β]
  have hlocal :
      ∀ i : P.Index,
        ((∑ b : Bool, if b then localPrimeWeight P β i else 1) : ℝ) =
          1 + localPrimeWeight P β i := by
    intro i
    simp
    ring
  rw [← Finset.prod_congr rfl (fun i _hi => hlocal i)]
  rw [← Finset.sum_prod_piFinset]
  rw [Fintype.piFinset_univ]

theorem fermionicSupertrace_eq_product
    (β : ℝ) :
    fermionicSupertrace P β =
      ∏ i : P.Index, (1 - localPrimeWeight P β i) := by
  classical
  unfold fermionicSupertrace fermionSign
  simp_rw [exp_neg_mul_bitEnergy_eq_profile_product P β]
  have hcombine :
      ∀ ε : P.Profile,
        (∏ i : P.Index, if ε i then (-1 : ℝ) else 1) *
          (∏ i : P.Index, if ε i then localPrimeWeight P β i else 1) =
        ∏ i : P.Index, if ε i then -localPrimeWeight P β i else 1 := by
    intro ε
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl ?_
    intro i _hi
    by_cases h : ε i <;> simp [h]
  simp_rw [hcombine]
  have hlocal :
      ∀ i : P.Index,
        ((∑ b : Bool, if b then -localPrimeWeight P β i else 1) : ℝ) =
          1 - localPrimeWeight P β i := by
    intro i
    simp
    ring
  rw [← Finset.prod_congr rfl (fun i _hi => hlocal i)]
  rw [← Finset.sum_prod_piFinset]
  rw [Fintype.piFinset_univ]

lemma fermionicPartition_pos (β : ℝ) :
    0 < fermionicPartition P β := by
  rw [fermionicPartition_eq_product]
  exact Finset.prod_pos (fun i _hi =>
    add_pos_of_pos_of_nonneg zero_lt_one (le_of_lt (localPrimeWeight_pos P β i)))

lemma fermionicPartition_ne_zero (β : ℝ) :
    fermionicPartition P β ≠ 0 :=
  (fermionicPartition_pos P β).ne'

lemma fermionicSupertrace_ne_zero
    (β : ℝ)
    (h : ∀ i : P.Index, (1 - localPrimeWeight P β i) ≠ 0) :
    fermionicSupertrace P β ≠ 0 := by
  rw [fermionicSupertrace_eq_product]
  exact Finset.prod_ne_zero_iff.mpr (fun i _hi => h i)

theorem primitiveMellinKernel_bitInteger_eq_exp_neg_mul_bitEnergy
    (ε : P.Profile)
    (β : ℝ)
    (hε : 1 < P.bitInteger ε) :
    primitiveMellinKernel (P.bitInteger ε) β =
      Real.exp (-β * P.bitEnergy ε) :=
  by
    exact
      PrimitiveBinarySuperZetaBridge.FinitePrimeBitLattice.primitiveMellinKernel_bitInteger_eq_exp_neg_mul_bitEnergy P ε β hε

end FinitePrimeBitLattice

end InfoGeometry.Arithmetic.PrimeFermionSupertraceFinite
