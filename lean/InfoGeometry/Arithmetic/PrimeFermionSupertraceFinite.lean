import InfoGeometry.Arithmetic.PrimitiveBinarySuperZetaBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# InfoGeometry.Arithmetic.PrimeFermionSupertraceFinite

Finite fermionic prime-bit partition and supertrace identities.

This sidecar proves the constructive finite Boolean product identities:

* unsigned square-free fermionic partition:
  `Σ_ε exp (-β * E ε) = Π_i (1 + exp (-β * log p_i))`;
* signed exterior/Möbius supertrace:
  `Σ_ε sign ε * exp (-β * E ε) = Π_i (1 - exp (-β * log p_i))`.

The finite bit-energy and primitive Mellin identities are owned by
`PrimitiveBinarySuperZetaBridge`.  This file does not assert infinite Euler
products, analytic continuation, RH, or a cohomological zero theorem.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Arithmetic.PrimeFermionSupertraceFinite

open InfoGeometry.Arithmetic.PrimitiveBinarySuperZetaBridge

namespace FinitePrimeBitLattice

variable (P : PrimitiveBinarySuperZetaBridge.FinitePrimeBitLattice)

/-- Local finite prime-bit Gibbs weight `exp (-β log p_i)`. -/
def localPrimeWeight
    (β : ℝ)
    (i : P.Index) : ℝ :=
  Real.exp (-β * Real.log (P.prime i : ℝ))

lemma localPrimeWeight_pos (β : ℝ) (i : P.Index) :
    0 < localPrimeWeight P β i := by
  unfold localPrimeWeight
  exact Real.exp_pos _

/-- Fermionic sign of a finite binary occupation profile. -/
def fermionSign
    (ε : P.Profile) : ℝ :=
  ∏ i : P.Index, if ε i then (-1 : ℝ) else 1

/-- Unsigned finite fermionic square-free primon partition. -/
def fermionicPartition
    (β : ℝ) : ℝ :=
  ∑ ε : P.Profile, Real.exp (-β * P.bitEnergy ε)

/-- Signed finite fermionic exterior/Möbius supertrace. -/
def fermionicSupertrace
    (β : ℝ) : ℝ :=
  ∑ ε : P.Profile, fermionSign P ε * Real.exp (-β * P.bitEnergy ε)

/-- The Gibbs factor of a profile factors into local prime-bit weights. -/
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

/--
Finite unsigned fermionic Euler product.

This is the finite square-free partition identity, the finite precursor of the
`ζ(s) / ζ(2s)` channel after an analytic infinite-product witness is supplied.
-/
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

/--
Finite signed fermionic Euler product.

This is the finite Möbius/supertrace identity, the finite precursor of the
`1 / ζ(s)` channel after an analytic infinite-product witness is supplied.
-/
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

/--
Primitive Mellin/Gibbs readout for the same finite profile, re-exported from
the primitive binary bridge.
-/
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
