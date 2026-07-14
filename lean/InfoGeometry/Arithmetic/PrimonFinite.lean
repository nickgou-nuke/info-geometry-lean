import Mathlib

/-!
# InfoGeometry.Arithmetic.PrimonFinite

Finite-mode algebra for the primon gas dictionary.

This file formalizes only the finite algebraic skeleton:

* fermionic states are finite subsets of a finite mode set;
* the unsigned fermionic partition is `∏ p, (1 + q p)`;
* the signed fermionic supertrace is `∏ p, (1 - q p)`;
* the finite boson/signed-fermion local cancellation is pointwise.

It does not assert an infinite Euler product, analytic continuation, zeta zero
statement, or cohomological interpretation.
-/

open scoped BigOperators

namespace PrimonFinite

variable {ι R : Type*}

/-- A fermionic Fock state is a finite subset of modes. -/
abbrev FState (ι : Type*) :=
  Finset ι

section Fermionic

variable [DecidableEq ι] [CommRing R]

/-- Multiplicative weight of a fermionic state. -/
def weight (q : ι → R) (S : FState ι) : R :=
  ∏ p ∈ S, q p

omit [DecidableEq ι] in
theorem weight_ne_zero [NoZeroDivisors R] [Nontrivial R]
    (q : ι → R) (S : FState ι)
    (h : ∀ p ∈ S, q p ≠ 0) :
    weight q S ≠ 0 := by
  unfold weight
  exact Finset.prod_ne_zero_iff.mpr h

/-- Fermion parity `(-1)^F`. -/
def parity (S : FState ι) : R :=
  (-1 : R) ^ S.card

/-- Ordinary fermionic partition function over a finite set of modes. -/
def ZF (modes : Finset ι) (q : ι → R) : R :=
  ∑ S ∈ modes.powerset, weight q S

/-- Fermionic supertrace / signed partition function. -/
def STrF (modes : Finset ι) (q : ι → R) : R :=
  ∑ S ∈ modes.powerset, parity S * weight q S

/--
Finite fermionic partition function:

`∑_{S ⊆ modes} ∏_{p ∈ S} q p = ∏_{p ∈ modes} (1 + q p)`.
-/
theorem ZF_eq_prod (modes : Finset ι) (q : ι → R) :
    ZF modes q = ∏ p ∈ modes, (1 + q p) := by
  classical
  refine Finset.induction_on modes ?empty ?insert
  · simp [ZF, weight]
  · intro a s ha ih
    unfold ZF
    rw [Finset.sum_powerset_insert ha]
    rw [Finset.prod_insert ha]
    have hsecond :
        (∑ t ∈ s.powerset, weight q (insert a t)) =
        q a * (∑ t ∈ s.powerset, weight q t) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro t ht
      have hat : a ∉ t := by
        intro hmem
        exact ha ((Finset.mem_powerset.mp ht) hmem)
      simp [weight, Finset.prod_insert hat]
    rw [hsecond]
    unfold ZF at ih
    rw [ih]
    ring

/-- Weighting by `-q` is the same as inserting fermion parity. -/
theorem weight_neg_eq_parity_mul_weight (q : ι → R) (S : FState ι) :
    weight (fun p => - q p) S = parity S * weight q S := by
  classical
  refine Finset.induction_on S ?empty ?insert
  · simp [weight, parity]
  · intro a s ha ih
    simp [weight, parity, Finset.prod_insert, ha, Finset.card_insert_of_notMem] at ih ⊢
    rw [ih]
    ring

/--
Finite fermionic supertrace:

`∑_{S ⊆ modes} (-1)^{|S|} ∏_{p ∈ S} q p = ∏_{p ∈ modes} (1 - q p)`.
-/
theorem STrF_eq_prod (modes : Finset ι) (q : ι → R) :
    STrF modes q = ∏ p ∈ modes, (1 - q p) := by
  classical
  calc
    STrF modes q = ZF modes (fun p => - q p) := by
      unfold STrF ZF
      refine Finset.sum_congr rfl ?_
      intro S _hS
      rw [weight_neg_eq_parity_mul_weight]
    _ = ∏ p ∈ modes, (1 + (-q p)) :=
      ZF_eq_prod modes (fun p => - q p)
    _ = ∏ p ∈ modes, (1 - q p) := by
      simp [sub_eq_add_neg]

/--
Möbius-type finite cancellation:

`∑_{S ⊆ modes} (-1)^|S| = 0` for nonempty `modes`.
-/
theorem finite_mobius_cancellation
    (modes : Finset ι)
    (h : modes.Nonempty) :
    (∑ S ∈ modes.powerset, parity (R := R) S) = 0 := by
  classical
  obtain ⟨a, ha⟩ := h
  have hprod : (∏ p ∈ modes, (1 - (1 : R))) = 0 := by
    simpa using
      (Finset.prod_eq_zero (s := modes) (f := fun _ : ι => (1 - (1 : R))) ha
        (by ring : (1 - (1 : R)) = 0))
  calc
    (∑ S ∈ modes.powerset, parity (R := R) S) =
        STrF modes (fun _ : ι => (1 : R)) := by
      simp [STrF, weight]
    _ = ∏ p ∈ modes, (1 - (1 : R)) :=
      STrF_eq_prod (modes := modes) (q := fun _ : ι => (1 : R))
    _ = 0 := hprod

end Fermionic

section Bosonic

variable {K : Type*} [Field K]

/-- Finite bosonic Euler factor. -/
def ZB (modes : Finset ι) (q : ι → K) : K :=
  ∏ p ∈ modes, (1 - q p)⁻¹

theorem ZB_ne_zero
    (modes : Finset ι) (q : ι → K)
    (h : ∀ p ∈ modes, (1 - q p) ≠ 0) :
    ZB modes q ≠ 0 := by
  unfold ZB
  exact Finset.prod_ne_zero_iff.mpr
    (fun p hp => inv_ne_zero (h p hp))

/-- Local finite supersymmetric cancellation of bosonic and signed fermionic factors. -/
theorem local_susy_cancellation
    (modes : Finset ι) (q : ι → K)
    (h : ∀ p ∈ modes, (1 - q p) ≠ 0) :
    ∏ p ∈ modes, ((1 - q p)⁻¹ * (1 - q p)) = 1 := by
  simpa using
    (Finset.prod_eq_one (s := modes)
      (f := fun p : ι => ((1 - q p)⁻¹ * (1 - q p)))
      (fun p hp => by simpa using inv_mul_cancel₀ (a := (1 - q p)) (h p hp)))

theorem ZB_mul_STrF_eq_one [DecidableEq ι]
    (modes : Finset ι) (q : ι → K)
    (h : ∀ p ∈ modes, (1 - q p) ≠ 0) :
    ZB modes q * STrF modes q = 1 := by
  rw [STrF_eq_prod]
  unfold ZB
  rw [← Finset.prod_mul_distrib]
  exact local_susy_cancellation modes q h

end Bosonic

end PrimonFinite
