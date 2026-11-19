/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Algebra.Group.Nat.TypeTags
import Mathlib.Algebra.Group.Irreducible.Defs
import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Algebra.BigOperators.Group.List.Defs
import Lean.Elab.Tactic.Omega

/-!
# A monoid with unique factorization, unbounded depth, and one irreducible

Source: *Complete Holographic White Paper*, version 6.1, section 4.1, page 16.
Associativity, an identity, unique factorization, and arbitrarily deep products
do not force infinitely many irreducibles or the prime-number asymptotic.

The carrier here is the native free cyclic monoid `Multiplicative ℕ`. Its
multiplication is addition of exponents, its identity has exponent zero, and
its unique irreducible has exponent one. We prove unique factorization as a
unique finite list of irreducibles, not as an assumed field of a structure.
No analytic counting theorem is claimed.

Mathlib's `UniqueFactorizationMonoid` typeclass requires a commutative monoid
with an absorbing zero. The ordinary monoid of this example has no absorbing
zero; the explicit factorization theorems express the needed property directly.
-/

namespace InfoGeometry.Holographic.MonoidCounterexample

open Multiplicative

/-- The single generator of the native free cyclic monoid. -/
def generator : Multiplicative ℕ := ofAdd 1

/-- In the free cyclic monoid, only exponent zero is invertible. -/
theorem isUnit_iff_toAdd_eq_zero (x : Multiplicative ℕ) :
    IsUnit x ↔ x.toAdd = 0 := by
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := hx.exists_right_inv
    have hsum := congrArg Multiplicative.toAdd hy
    simp only [toAdd_mul, toAdd_one] at hsum
    omega
  · intro hx
    have hxone : x = 1 := Multiplicative.ext hx
    rw [hxone]
    exact isUnit_one

/-- Exponent one cannot be decomposed into two nonunit factors. -/
theorem generator_irreducible : Irreducible generator := by
  refine ⟨?_, ?_⟩
  · rw [isUnit_iff_toAdd_eq_zero]
    change (1 : ℕ) ≠ 0
    decide
  · intro a b hab
    have hsum : 1 = a.toAdd + b.toAdd := by
      simpa [generator] using congrArg Multiplicative.toAdd hab
    have hzero : a.toAdd = 0 ∨ b.toAdd = 0 := by omega
    exact hzero.imp (isUnit_iff_toAdd_eq_zero a).mpr
      (isUnit_iff_toAdd_eq_zero b).mpr

/-- There is exactly one possible irreducible element. -/
theorem irreducible_iff_eq_generator (x : Multiplicative ℕ) :
    Irreducible x ↔ x = generator := by
  constructor
  · intro hx
    have hxzero : x.toAdd ≠ 0 := by
      intro hzero
      exact hx.not_isUnit ((isUnit_iff_toAdd_eq_zero x).mpr hzero)
    have hfactor : x = generator * ofAdd (x.toAdd - 1) := by
      apply Multiplicative.ext
      change x.toAdd = 1 + (x.toAdd - 1)
      omega
    rcases hx.isUnit_or_isUnit hfactor with hunit | hunit
    · exact (generator_irreducible.not_isUnit hunit).elim
    · have hpred : x.toAdd - 1 = 0 :=
        (isUnit_iff_toAdd_eq_zero (ofAdd (x.toAdd - 1))).mp hunit
      apply Multiplicative.ext
      change x.toAdd = 1
      omega
  · rintro rfl
    exact generator_irreducible

/-- The set of irreducibles consists of the single generator. -/
theorem existsUnique_irreducible : ∃! q : Multiplicative ℕ, Irreducible q := by
  exact ⟨generator, generator_irreducible,
    fun q hq => (irreducible_iff_eq_generator q).mp hq⟩

/-- Taking a power records precisely its natural-number exponent. -/
@[simp] theorem generator_pow (n : ℕ) : generator ^ n = ofAdd n := by
  apply Multiplicative.ext
  simp [generator]

/-- Distinct exponents give distinct elements, so the powers have unbounded depth. -/
theorem generator_pow_injective :
    Function.Injective (fun n : ℕ => generator ^ n) := by
  intro m n h
  have hnat := congrArg Multiplicative.toAdd h
  simpa only [generator_pow, toAdd_ofAdd] using hnat

/-- Every element has a unique expression as a power of the single generator. -/
theorem existsUnique_generator_pow (x : Multiplicative ℕ) :
    ∃! n : ℕ, x = generator ^ n := by
  refine ⟨x.toAdd, ?_, ?_⟩
  · simp
  · intro n hn
    have hnat := congrArg Multiplicative.toAdd hn
    simpa only [generator_pow, toAdd_ofAdd] using hnat.symm

/-- Divisibility of powers is exactly the usual order on their exponents. -/
theorem generator_pow_dvd_iff (m n : ℕ) :
    generator ^ m ∣ generator ^ n ↔ m ≤ n := by
  constructor
  · rintro ⟨x, hx⟩
    have hnat := congrArg Multiplicative.toAdd hx
    simp only [toAdd_mul, generator_pow, toAdd_ofAdd] at hnat
    omega
  · intro hmn
    refine ⟨ofAdd (n - m), ?_⟩
    apply Multiplicative.ext
    simp only [toAdd_mul, generator_pow, toAdd_ofAdd]
    omega

/-- Every stage has a strictly deeper stage in the divisibility order. -/
theorem generator_powers_strict_divisibility (n : ℕ) :
    generator ^ n ∣ generator ^ (n + 1) ∧
      ¬generator ^ (n + 1) ∣ generator ^ n := by
  rw [generator_pow_dvd_iff, generator_pow_dvd_iff]
  omega

/-- Every list of irreducibles is the corresponding repetition of the sole generator. -/
theorem irreducible_list_eq_replicate (f : List (Multiplicative ℕ))
    (hf : ∀ a ∈ f, Irreducible a) :
    f = List.replicate f.length generator := by
  exact List.eq_replicate_iff.mpr
    ⟨rfl, fun a ha => (irreducible_iff_eq_generator a).mp (hf a ha)⟩

/-- Equal products of irreducible lists have exactly the same factorization. -/
theorem irreducible_factorization_unique (f g : List (Multiplicative ℕ))
    (hf : ∀ a ∈ f, Irreducible a) (hg : ∀ a ∈ g, Irreducible a)
    (hprod : f.prod = g.prod) : f = g := by
  have hfpow : f.prod = generator ^ f.length :=
    List.prod_eq_pow_length f generator
      (fun a ha => (irreducible_iff_eq_generator a).mp (hf a ha))
  have hgpow : g.prod = generator ^ g.length :=
    List.prod_eq_pow_length g generator
      (fun a ha => (irreducible_iff_eq_generator a).mp (hg a ha))
  have hlength : f.length = g.length :=
    generator_pow_injective (hfpow.symm.trans (hprod.trans hgpow))
  calc
    f = List.replicate f.length generator := irreducible_list_eq_replicate f hf
    _ = List.replicate g.length generator := by rw [hlength]
    _ = g := (irreducible_list_eq_replicate g hg).symm

/-- Every element has a unique finite factorization into irreducibles. -/
theorem existsUnique_irreducible_factorization (x : Multiplicative ℕ) :
    ∃! f : List (Multiplicative ℕ), (∀ a ∈ f, Irreducible a) ∧ f.prod = x := by
  let factors := List.replicate x.toAdd generator
  have hfactors : ∀ a ∈ factors, Irreducible a := by
    intro a ha
    have heq : a = generator := (List.mem_replicate.mp ha).2
    exact (irreducible_iff_eq_generator a).mpr heq
  have hprod : factors.prod = x := by
    simp [factors, ofAdd_toAdd]
  refine ⟨factors, ⟨hfactors, hprod⟩, ?_⟩
  intro g hg
  exact irreducible_factorization_unique g factors hg.1 hfactors (hg.2.trans hprod.symm)

end InfoGeometry.Holographic.MonoidCounterexample
