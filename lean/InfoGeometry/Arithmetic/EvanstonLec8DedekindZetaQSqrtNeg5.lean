/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import InfoGeometry.Canonical.KleinEvanston1893MoebiusAndSixPillarMasterSynthesis
import InfoGeometry.Arithmetic.NumberFieldDedekindZetaEulerProduct
import InfoGeometry.Arithmetic.NumberFieldHeckeLFunction

/-!
# Evanston Lecture VIII, Ideal Factorization in `ℤ[√-5]`, and Dedekind Zeta

## i. Overview

This module bridges the finite `ZSqrtNeg5` non-unique factorization witness in
`KleinEvanston1893MoebiusAndSixPillarMasterSynthesis` to Mathlib's `Zsqrtd (-5)`
ring, establishes the explicit maximal-ideal factorization of
`2 * 3 = (1 + √-5)(1 - √-5)` in `Ideal (Zsqrtd (-5))` together with quotient
isomorphisms to `ZMod 2` and `ZMod 3` and non-principality of `p2`, `p3`,
`p3'`, and links these ideals to `HeightOneSpectrum (𝓞 K)`,
`dedekindZeta_hasProd`, and `NumberField.heckeLSeries_one_eq_dedekindZeta`,
including a concrete `AdjoinRoot (X ^ 2 + C 5 : ℚ[X])` realization of `ℚ(√-5)`.
It does not assert the global splitting identity
`dedekindZeta ℚ(√-5) s = riemannZeta s * L(χ_{-20}, s)`.

## ii. Key results

- `instNoZeroDivisorsZsqrtdNeg5`: scoped `NoZeroDivisors (Zsqrtd (-5))`
  instance (absent from Mathlib for negative `d`).
- `zSqrtNeg5EquivZsqrtd`: equivalence `ZSqrtNeg5 ≃ Zsqrtd (-5)` preserving
  multiplication, norm, and `evanston_lec8_nonunique_factorization_and_ideal_norm`.
- `p2_sq_eq_span_two`, `p3_mul_p3'_eq_span_three`, `p2_mul_p3_eq_span`,
  `p2_mul_p3'_eq_span`: explicit ideal factorization in `Ideal (Zsqrtd (-5))`.
- `p2_quotient_equiv_zmod2`, `p3_quotient_equiv_zmod3`,
  `p3'_quotient_equiv_zmod3`, `p2_not_principal`: maximality, distinctness,
  and non-principality.
- `place2`, `place3`, `place3'` & `ringOfIntegersEquivZsqrtdNeg5`: transport to
  `HeightOneSpectrum (𝓞 K)` and concrete `ℚ(√-5)` Dedekind zeta / Hecke
  Euler-product bridge.

## iii. Table of contents

1. Scoped domain instance and `ZSqrtNeg5 ≃ Zsqrtd (-5)` bridge.
2. Explicit ideal factorization, `ZMod` quotients, and non-principality.
3. Number-field `HeightOneSpectrum` transport and concrete `ℚ(√-5)` Euler
   product bridge.

## iv. References

- `InfoGeometry.Canonical.KleinEvanston1893MoebiusAndSixPillarMasterSynthesis`
- `InfoGeometry.Arithmetic.NumberFieldDedekindZetaEulerProduct`
- `InfoGeometry.Arithmetic.NumberFieldHeckeLFunction`
-/

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Arithmetic.EvanstonLec8DedekindZetaQSqrtNeg5

open Ideal NumberField IsDedekindDomain Polynomial
open InfoGeometry.Canonical.KleinEvanston1893MoebiusAndSixPillarMasterSynthesis
open InfoGeometry.Arithmetic.NumberFieldDedekindZetaEulerProduct

/-! ### 1. Scoped Domain Instance and `ZSqrtNeg5 ≃ Zsqrtd (-5)` Bridge -/

/-- Scoped `NoZeroDivisors` instance for `Zsqrtd (-5)`, proved via the
multiplicative norm `Zsqrtd.norm_mul` and `Zsqrtd.norm_eq_zero`. -/
scoped instance instNoZeroDivisorsZsqrtdNeg5 : NoZeroDivisors (Zsqrtd (-5)) where
  eq_zero_or_eq_zero_of_mul_eq_zero {a b} h := by
    have hd : ∀ n : ℤ, (-5 : ℤ) ≠ n * n := fun n hn => by nlinarith
    have hnorm : a.norm * b.norm = 0 := by
      rw [← Zsqrtd.norm_mul, h, Zsqrtd.norm_zero]
    rcases mul_eq_zero.mp hnorm with ha | hb
    · exact Or.inl ((Zsqrtd.norm_eq_zero hd a).mp ha)
    · exact Or.inr ((Zsqrtd.norm_eq_zero hd b).mp hb)

/-- Scoped `IsDomain` instance for `Zsqrtd (-5)`. -/
scoped instance instIsDomainZsqrtdNeg5 : IsDomain (Zsqrtd (-5)) :=
  NoZeroDivisors.to_isDomain _

/-- Equivalence between `ZSqrtNeg5` (`ℤ × ℤ`) and Mathlib's `Zsqrtd (-5)`. -/
def zSqrtNeg5EquivZsqrtd : ZSqrtNeg5 ≃ Zsqrtd (-5) where
  toFun u := ⟨u.1, u.2⟩
  invFun z := (z.re, z.im)
  left_inv _ := rfl
  right_inv _ := rfl

/-- `zSqrtNeg5EquivZsqrtd` intertwines `zSqrtNeg5Mul` with multiplication in `Zsqrtd (-5)`. -/
lemma zSqrtNeg5EquivZsqrtd_mul (u v : ZSqrtNeg5) :
    zSqrtNeg5EquivZsqrtd (zSqrtNeg5Mul u v) =
      zSqrtNeg5EquivZsqrtd u * zSqrtNeg5EquivZsqrtd v := by
  ext
  · simp [zSqrtNeg5EquivZsqrtd, zSqrtNeg5Mul]
    ring
  · simp [zSqrtNeg5EquivZsqrtd, zSqrtNeg5Mul]

/-- `zSqrtNeg5EquivZsqrtd` identifies `zSqrtNeg5Norm` with `Zsqrtd.norm`. -/
lemma zSqrtNeg5EquivZsqrtd_norm (u : ZSqrtNeg5) :
    Zsqrtd.norm (zSqrtNeg5EquivZsqrtd u) = zSqrtNeg5Norm u := by
  dsimp [zSqrtNeg5EquivZsqrtd, Zsqrtd.norm, zSqrtNeg5Norm]
  ring

/-- `zSqrtNeg5EquivZsqrtd` preserves the four Evanston Lecture VIII witness elements
and their product `6`. -/
lemma zSqrtNeg5EquivZsqrtd_witnesses :
    zSqrtNeg5EquivZsqrtd (2, 0) = 2 ∧
    zSqrtNeg5EquivZsqrtd (3, 0) = 3 ∧
    zSqrtNeg5EquivZsqrtd (1, 1) = ⟨1, 1⟩ ∧
    zSqrtNeg5EquivZsqrtd (1, -1) = ⟨1, -1⟩ ∧
    zSqrtNeg5EquivZsqrtd (6, 0) = 6 ∧
    (⟨1, 1⟩ : Zsqrtd (-5)) = 1 + Zsqrtd.sqrtd ∧
    (⟨1, -1⟩ : Zsqrtd (-5)) = 1 - Zsqrtd.sqrtd := by
  refine ⟨?_, ?_, rfl, rfl, ?_, ?_, ?_⟩ <;> ext <;> decide

/-- Transport of `evanston_lec8_nonunique_factorization_and_ideal_norm` from
`ZSqrtNeg5` to `Zsqrtd (-5)`: norm multiplicativity, unit characterization,
absence of elements of norm `2` or `3`, irreducibility and non-association of
`2`, `3`, `1 + √-5`, `1 - √-5`, and `2 * 3 = 6 = (1 + √-5) * (1 - √-5)`. -/
lemma zsqrtdNeg5_evanston_lec8_nonunique_factorization :
    (∀ u v : Zsqrtd (-5), (u * v).norm = u.norm * v.norm) ∧
    (∀ u : Zsqrtd (-5), u.norm = 1 ↔ u = 1 ∨ u = -1) ∧
    (∀ u : Zsqrtd (-5), u.norm ≠ 2 ∧ u.norm ≠ 3) ∧
    (∀ u v : Zsqrtd (-5), u * v = 2 → u.norm = 1 ∨ v.norm = 1) ∧
    (∀ u v : Zsqrtd (-5), u * v = 3 → u.norm = 1 ∨ v.norm = 1) ∧
    (∀ u v : Zsqrtd (-5), u * v = ⟨1, 1⟩ → u.norm = 1 ∨ v.norm = 1) ∧
    (∀ u v : Zsqrtd (-5), u * v = ⟨1, -1⟩ → u.norm = 1 ∨ v.norm = 1) ∧
    (2 : Zsqrtd (-5)) * 3 = 6 ∧
    (⟨1, 1⟩ : Zsqrtd (-5)) * ⟨1, -1⟩ = 6 ∧
    ¬ ∃ e : Zsqrtd (-5), e.norm = 1 ∧ (e * 2 = ⟨1, 1⟩ ∨ e * 3 = ⟨1, 1⟩) := by
  have h := evanston_lec8_nonunique_factorization_and_ideal_norm
  rcases h with ⟨hmul, hunit, h23, hirr2, hirr3, hirr1p, hirr1m, h23_6, h1pm_6, hno⟩
  have hconv : ∀ u : Zsqrtd (-5),
      zSqrtNeg5Norm (zSqrtNeg5EquivZsqrtd.symm u) = u.norm := by
    intro u
    rw [← zSqrtNeg5EquivZsqrtd_norm]
    rfl
  refine ⟨Zsqrtd.norm_mul, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u
    rw [← hconv u, hunit]
    constructor
    · rintro (hu | hu)
      · left; exact zSqrtNeg5EquivZsqrtd.symm.injective (by simpa [zSqrtNeg5EquivZsqrtd] using hu)
      · right; exact zSqrtNeg5EquivZsqrtd.symm.injective (by simpa [zSqrtNeg5EquivZsqrtd] using hu)
    · rintro (rfl | rfl)
      · left; rfl
      · right; rfl
  · intro u
    rw [← hconv u]
    exact h23 (zSqrtNeg5EquivZsqrtd.symm u)
  · intro u v huv
    have huv' : zSqrtNeg5Mul (zSqrtNeg5EquivZsqrtd.symm u)
        (zSqrtNeg5EquivZsqrtd.symm v) = (2, 0) := by
      apply zSqrtNeg5EquivZsqrtd.injective
      rw [zSqrtNeg5EquivZsqrtd_mul]
      simpa [zSqrtNeg5EquivZsqrtd_witnesses.1] using huv
    simpa [hconv] using hirr2 _ _ huv'
  · intro u v huv
    have huv' : zSqrtNeg5Mul (zSqrtNeg5EquivZsqrtd.symm u)
        (zSqrtNeg5EquivZsqrtd.symm v) = (3, 0) := by
      apply zSqrtNeg5EquivZsqrtd.injective
      rw [zSqrtNeg5EquivZsqrtd_mul]
      simpa [zSqrtNeg5EquivZsqrtd_witnesses.2.1] using huv
    simpa [hconv] using hirr3 _ _ huv'
  · intro u v huv
    have huv' : zSqrtNeg5Mul (zSqrtNeg5EquivZsqrtd.symm u)
        (zSqrtNeg5EquivZsqrtd.symm v) = (1, 1) := by
      apply zSqrtNeg5EquivZsqrtd.injective
      rw [zSqrtNeg5EquivZsqrtd_mul]
      simpa [zSqrtNeg5EquivZsqrtd] using huv
    simpa [hconv] using hirr1p _ _ huv'
  · intro u v huv
    have huv' : zSqrtNeg5Mul (zSqrtNeg5EquivZsqrtd.symm u)
        (zSqrtNeg5EquivZsqrtd.symm v) = (1, -1) := by
      apply zSqrtNeg5EquivZsqrtd.injective
      rw [zSqrtNeg5EquivZsqrtd_mul]
      simpa [zSqrtNeg5EquivZsqrtd] using huv
    simpa [hconv] using hirr1m _ _ huv'
  · ext <;> decide
  · ext <;> decide
  · rintro ⟨e, he1, heq⟩
    refine hno ⟨zSqrtNeg5EquivZsqrtd.symm e, ?_, ?_⟩
    · rwa [hconv e]
    · rcases heq with h2 | h3
      · left
        apply zSqrtNeg5EquivZsqrtd.injective
        rw [zSqrtNeg5EquivZsqrtd_mul, zSqrtNeg5EquivZsqrtd.apply_symm_apply,
          zSqrtNeg5EquivZsqrtd_witnesses.1]
        exact h2
      · right
        apply zSqrtNeg5EquivZsqrtd.injective
        rw [zSqrtNeg5EquivZsqrtd_mul, zSqrtNeg5EquivZsqrtd.apply_symm_apply,
          zSqrtNeg5EquivZsqrtd_witnesses.2.1]
        exact h3

/-- Characterization of units in `Zsqrtd (-5)` (`±1`) and non-existence of norm `2` or `3`. -/
lemma zsqrtdNeg5_isUnit_iff_and_no_norm_two_three (u : Zsqrtd (-5)) :
    (IsUnit u ↔ u = 1 ∨ u = -1) ∧ u.norm ≠ 2 ∧ u.norm ≠ 3 := by
  have h := zsqrtdNeg5_evanston_lec8_nonunique_factorization
  refine ⟨?_, h.2.2.1 u⟩
  rw [← Zsqrtd.norm_eq_one_iff' (by norm_num) u]
  exact h.2.1 u

/-! ### 2. Explicit Ideal Factorization, `ZMod` Quotients, and Non-Principality -/

/-- Prime ideal `p₂ = (2, 1 + √-5)` above `2` in `Zsqrtd (-5)`. -/
def p2 : Ideal (Zsqrtd (-5)) := Ideal.span {2, ⟨1, 1⟩}

/-- Prime ideal `p₃ = (3, 1 + √-5)` above `3` in `Zsqrtd (-5)`. -/
def p3 : Ideal (Zsqrtd (-5)) := Ideal.span {3, ⟨1, 1⟩}

/-- Conjugate prime ideal `p₃' = (3, 1 - √-5)` above `3` in `Zsqrtd (-5)`. -/
def p3' : Ideal (Zsqrtd (-5)) := Ideal.span {3, ⟨1, -1⟩}

/-- Exact ideal factorization `p₂² = (2)` in `Ideal (Zsqrtd (-5))`. -/
lemma p2_sq_eq_span_two : p2 ^ 2 = Ideal.span {(2 : Zsqrtd (-5))} := by
  rw [sq, p2, Ideal.span_pair_mul_span_pair]
  apply le_antisymm
  · rw [Ideal.span_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact Ideal.mem_span_singleton.mpr ⟨2, rfl⟩
    · exact Ideal.mem_span_singleton.mpr ⟨⟨1, 1⟩, rfl⟩
    · exact Ideal.mem_span_singleton.mpr ⟨⟨1, 1⟩, mul_comm _ _⟩
    · refine Ideal.mem_span_singleton.mpr ⟨⟨-2, 1⟩, ?_⟩
      ext <;> decide
  · rw [Ideal.span_singleton_le_iff_mem]
    have hmem : (2 : Zsqrtd (-5)) * ⟨1, 1⟩ - ⟨1, 1⟩ * ⟨1, 1⟩ - 2 * 2 ∈
        Ideal.span ({2 * 2, 2 * ⟨1, 1⟩, ⟨1, 1⟩ * 2, ⟨1, 1⟩ * ⟨1, 1⟩} :
          Set (Zsqrtd (-5))) :=
      Ideal.sub_mem _ (Ideal.sub_mem _
        (Ideal.subset_span (by simp))
        (Ideal.subset_span (by simp)))
        (Ideal.subset_span (by simp))
    convert hmem using 1
    ext <;> decide

/-- Exact ideal factorization `p₃ * p₃' = (3)` in `Ideal (Zsqrtd (-5))`. -/
lemma p3_mul_p3'_eq_span_three : p3 * p3' = Ideal.span {(3 : Zsqrtd (-5))} := by
  rw [p3, p3', Ideal.span_pair_mul_span_pair]
  apply le_antisymm
  · rw [Ideal.span_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact Ideal.mem_span_singleton.mpr ⟨3, rfl⟩
    · exact Ideal.mem_span_singleton.mpr ⟨⟨1, -1⟩, rfl⟩
    · exact Ideal.mem_span_singleton.mpr ⟨⟨1, 1⟩, mul_comm _ _⟩
    · refine Ideal.mem_span_singleton.mpr ⟨2, ?_⟩
      ext <;> decide
  · rw [Ideal.span_singleton_le_iff_mem]
    have hmem : (3 : Zsqrtd (-5)) * 3 - ⟨1, 1⟩ * ⟨1, -1⟩ ∈
        Ideal.span ({3 * 3, 3 * ⟨1, -1⟩, ⟨1, 1⟩ * 3, ⟨1, 1⟩ * ⟨1, -1⟩} :
          Set (Zsqrtd (-5))) :=
      Ideal.sub_mem _ (Ideal.subset_span (by simp)) (Ideal.subset_span (by simp))
    convert hmem using 1
    ext <;> decide

/-- Exact ideal factorization `p₂ * p₃ = (1 + √-5)` in `Ideal (Zsqrtd (-5))`. -/
lemma p2_mul_p3_eq_span : p2 * p3 = Ideal.span {(⟨1, 1⟩ : Zsqrtd (-5))} := by
  rw [p2, p3, Ideal.span_pair_mul_span_pair]
  apply le_antisymm
  · rw [Ideal.span_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · refine Ideal.mem_span_singleton.mpr ⟨⟨1, -1⟩, ?_⟩
      ext <;> decide
    · exact Ideal.mem_span_singleton.mpr ⟨2, mul_comm _ _⟩
    · exact Ideal.mem_span_singleton.mpr ⟨3, rfl⟩
    · exact Ideal.mem_span_singleton.mpr ⟨⟨1, 1⟩, rfl⟩
  · rw [Ideal.span_singleton_le_iff_mem]
    have hmem : (⟨1, 1⟩ : Zsqrtd (-5)) * 3 - 2 * ⟨1, 1⟩ ∈
        Ideal.span ({2 * 3, 2 * ⟨1, 1⟩, ⟨1, 1⟩ * 3, ⟨1, 1⟩ * ⟨1, 1⟩} :
          Set (Zsqrtd (-5))) :=
      Ideal.sub_mem _ (Ideal.subset_span (by simp)) (Ideal.subset_span (by simp))
    convert hmem using 1
    ext <;> decide

/-- Exact ideal factorization `p₂ * p₃' = (1 - √-5)` in `Ideal (Zsqrtd (-5))`. -/
lemma p2_mul_p3'_eq_span : p2 * p3' = Ideal.span {(⟨1, -1⟩ : Zsqrtd (-5))} := by
  rw [p2, p3', Ideal.span_pair_mul_span_pair]
  apply le_antisymm
  · rw [Ideal.span_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · refine Ideal.mem_span_singleton.mpr ⟨⟨1, 1⟩, ?_⟩
      ext <;> decide
    · exact Ideal.mem_span_singleton.mpr ⟨2, mul_comm _ _⟩
    · refine Ideal.mem_span_singleton.mpr ⟨⟨-2, 1⟩, ?_⟩
      ext <;> decide
    · exact Ideal.mem_span_singleton.mpr ⟨⟨1, 1⟩, mul_comm _ _⟩
  · rw [Ideal.span_singleton_le_iff_mem]
    have hmem : (2 : Zsqrtd (-5)) * 3 - ⟨1, 1⟩ * 3 - 2 * ⟨1, -1⟩ ∈
        Ideal.span ({2 * 3, 2 * ⟨1, -1⟩, ⟨1, 1⟩ * 3, ⟨1, 1⟩ * ⟨1, -1⟩} :
          Set (Zsqrtd (-5))) :=
      Ideal.sub_mem _
        (Ideal.sub_mem _ (Ideal.subset_span (by simp)) (Ideal.subset_span (by simp)))
        (Ideal.subset_span (by simp))
    convert hmem using 1
    ext <;> decide

/-- Principal ideal equality `(2) * (3) = (1 + √-5) * (1 - √-5)` via prime ideal
recombination `(p₂²) * (p₃ * p₃') = (p₂ * p₃) * (p₂ * p₃')`. -/
lemma ideal_two_mul_three_eq_one_plus_mul_one_minus :
    Ideal.span {(2 : Zsqrtd (-5))} * Ideal.span {(3 : Zsqrtd (-5))} =
      Ideal.span {(⟨1, 1⟩ : Zsqrtd (-5))} * Ideal.span {(⟨1, -1⟩ : Zsqrtd (-5))} := by
  rw [← p2_sq_eq_span_two, ← p3_mul_p3'_eq_span_three,
    ← p2_mul_p3_eq_span, ← p2_mul_p3'_eq_span]
  ring

/-- Canonical ring homomorphism `Zsqrtd (-5) →+* ZMod 2` mapping `√-5 ↦ 1`. -/
def phi2 : Zsqrtd (-5) →+* ZMod 2 :=
  Zsqrtd.lift ⟨1, by decide⟩

/-- Canonical ring homomorphism `Zsqrtd (-5) →+* ZMod 3` mapping `√-5 ↦ -1`. -/
def phi3 : Zsqrtd (-5) →+* ZMod 3 :=
  Zsqrtd.lift ⟨-1, by decide⟩

/-- Canonical ring homomorphism `Zsqrtd (-5) →+* ZMod 3` mapping `√-5 ↦ 1`. -/
def phi3' : Zsqrtd (-5) →+* ZMod 3 :=
  Zsqrtd.lift ⟨1, by decide⟩

lemma phi2_surjective : Function.Surjective phi2 := by
  intro y
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective y
  exact ⟨(k : Zsqrtd (-5)), by simp⟩

lemma phi3_surjective : Function.Surjective phi3 := by
  intro y
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective y
  exact ⟨(k : Zsqrtd (-5)), by simp⟩

lemma phi3'_surjective : Function.Surjective phi3' := by
  intro y
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective y
  exact ⟨(k : Zsqrtd (-5)), by simp⟩

lemma ker_phi2_eq_p2 : RingHom.ker phi2 = p2 := by
  apply le_antisymm
  · intro z hz
    rw [RingHom.mem_ker] at hz
    have hsum : ((z.re + z.im : ℤ) : ZMod 2) = 0 := by
      simpa [phi2, Zsqrtd.lift_apply_apply] using hz
    obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (z.re + z.im) 2).mp hsum
    push_cast at hk
    have hz_eq : ((k - z.im : ℤ) : Zsqrtd (-5)) * 2 +
        ((z.im : ℤ) : Zsqrtd (-5)) * ⟨1, 1⟩ = z := by
      ext
      · simp
        linarith
      · simp
    rw [p2, Ideal.mem_span_pair]
    exact ⟨_, _, hz_eq⟩
  · rw [p2, Ideal.span_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · simp only [SetLike.mem_coe, RingHom.mem_ker]; simp [phi2]; decide
    · simp only [SetLike.mem_coe, RingHom.mem_ker]; simp [phi2]; decide

lemma ker_phi3_eq_p3 : RingHom.ker phi3 = p3 := by
  apply le_antisymm
  · intro z hz
    rw [RingHom.mem_ker] at hz
    have hdiff : ((z.re - z.im : ℤ) : ZMod 3) = 0 := by
      simpa [phi3, Zsqrtd.lift_apply_apply, sub_eq_add_neg] using hz
    obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (z.re - z.im) 3).mp hdiff
    push_cast at hk
    have hz_eq : ((k : ℤ) : Zsqrtd (-5)) * 3 +
        ((z.im : ℤ) : Zsqrtd (-5)) * ⟨1, 1⟩ = z := by
      ext
      · simp
        linarith
      · simp
    rw [p3, Ideal.mem_span_pair]
    exact ⟨_, _, hz_eq⟩
  · rw [p3, Ideal.span_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · simp only [SetLike.mem_coe, RingHom.mem_ker]; simp [phi3]; decide
    · simp only [SetLike.mem_coe, RingHom.mem_ker]; simp [phi3]

lemma ker_phi3'_eq_p3' : RingHom.ker phi3' = p3' := by
  apply le_antisymm
  · intro z hz
    rw [RingHom.mem_ker] at hz
    have hsum : ((z.re + z.im : ℤ) : ZMod 3) = 0 := by
      simpa [phi3', Zsqrtd.lift_apply_apply] using hz
    obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (z.re + z.im) 3).mp hsum
    push_cast at hk
    have hz_eq : ((k : ℤ) : Zsqrtd (-5)) * 3 +
        ((-z.im : ℤ) : Zsqrtd (-5)) * ⟨1, -1⟩ = z := by
      ext
      · simp
        linarith
      · simp
    rw [p3', Ideal.mem_span_pair]
    exact ⟨_, _, hz_eq⟩
  · rw [p3', Ideal.span_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · simp only [SetLike.mem_coe, RingHom.mem_ker]; simp [phi3']; decide
    · simp only [SetLike.mem_coe, RingHom.mem_ker]; simp [phi3']

/-- Quotient ring isomorphism `Zsqrtd (-5) ⧸ p₂ ≃+* ZMod 2`. -/
def p2QuotientEquivZMod2 : Zsqrtd (-5) ⧸ p2 ≃+* ZMod 2 :=
  (Ideal.quotEquivOfEq ker_phi2_eq_p2.symm).trans
    (RingHom.quotientKerEquivOfSurjective phi2_surjective)

/-- Quotient ring isomorphism `Zsqrtd (-5) ⧸ p₃ ≃+* ZMod 3`. -/
def p3QuotientEquivZMod3 : Zsqrtd (-5) ⧸ p3 ≃+* ZMod 3 :=
  (Ideal.quotEquivOfEq ker_phi3_eq_p3.symm).trans
    (RingHom.quotientKerEquivOfSurjective phi3_surjective)

/-- Quotient ring isomorphism `Zsqrtd (-5) ⧸ p₃' ≃+* ZMod 3`. -/
def p3'QuotientEquivZMod3 : Zsqrtd (-5) ⧸ p3' ≃+* ZMod 3 :=
  (Ideal.quotEquivOfEq ker_phi3'_eq_p3'.symm).trans
    (RingHom.quotientKerEquivOfSurjective phi3'_surjective)

/-- Maximality, nonzero status, and pairwise distinctness of `p2`, `p3`, `p3'`. -/
lemma p2_p3_p3'_maximal_ne_bot_pairwise_ne :
    p2.IsMaximal ∧ p3.IsMaximal ∧ p3'.IsMaximal ∧
    p2 ≠ ⊥ ∧ p3 ≠ ⊥ ∧ p3' ≠ ⊥ ∧
    p2 ≠ p3 ∧ p2 ≠ p3' ∧ p3 ≠ p3' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp2_max : p2.IsMaximal := by
    rw [← ker_phi2_eq_p2, RingHom.ker_eq_comap_bot]
    exact Ideal.comap_isMaximal_of_surjective phi2 phi2_surjective
  have hp3_max : p3.IsMaximal := by
    rw [← ker_phi3_eq_p3, RingHom.ker_eq_comap_bot]
    exact Ideal.comap_isMaximal_of_surjective phi3 phi3_surjective
  have hp3'_max : p3'.IsMaximal := by
    rw [← ker_phi3'_eq_p3', RingHom.ker_eq_comap_bot]
    exact Ideal.comap_isMaximal_of_surjective phi3' phi3'_surjective
  have hp2_bot : p2 ≠ ⊥ := by
    intro h
    have h2 : (2 : Zsqrtd (-5)) ∈ p2 := Ideal.subset_span (by simp)
    rw [h, Ideal.mem_bot] at h2
    have : (2 : ℤ) = 0 := congrArg Zsqrtd.re h2
    norm_num at this
  have hp3_bot : p3 ≠ ⊥ := by
    intro h
    have h3 : (3 : Zsqrtd (-5)) ∈ p3 := Ideal.subset_span (by simp)
    rw [h, Ideal.mem_bot] at h3
    have : (3 : ℤ) = 0 := congrArg Zsqrtd.re h3
    norm_num at this
  have hp3'_bot : p3' ≠ ⊥ := by
    intro h
    have h3 : (3 : Zsqrtd (-5)) ∈ p3' := Ideal.subset_span (by simp)
    rw [h, Ideal.mem_bot] at h3
    have : (3 : ℤ) = 0 := congrArg Zsqrtd.re h3
    norm_num at this
  have h23 : p2 ≠ p3 := by
    intro h
    have h2 : (2 : Zsqrtd (-5)) ∈ p3 := h ▸ Ideal.subset_span (by simp)
    rw [← ker_phi3_eq_p3, RingHom.mem_ker] at h2
    have hval : phi3 2 = (2 : ZMod 3) := by simp [phi3]
    rw [h2] at hval
    have hv := congrArg ZMod.val hval
    change (0 : ℕ) = 2 at hv
    omega
  have h23' : p2 ≠ p3' := by
    intro h
    have h2 : (2 : Zsqrtd (-5)) ∈ p3' := h ▸ Ideal.subset_span (by simp)
    rw [← ker_phi3'_eq_p3', RingHom.mem_ker] at h2
    have hval : phi3' 2 = (2 : ZMod 3) := by simp [phi3']
    rw [h2] at hval
    have hv := congrArg ZMod.val hval
    change (0 : ℕ) = 2 at hv
    omega
  have h33' : p3 ≠ p3' := by
    intro h
    have h1p : (⟨1, 1⟩ : Zsqrtd (-5)) ∈ p3' := h ▸ Ideal.subset_span (by simp)
    rw [← ker_phi3'_eq_p3', RingHom.mem_ker] at h1p
    have hval : phi3' ⟨1, 1⟩ = (2 : ZMod 3) := by
      simp only [phi3', Zsqrtd.lift_apply_apply]
      norm_num
    rw [h1p] at hval
    have hv := congrArg ZMod.val hval
    change (0 : ℕ) = 2 at hv
    omega
  exact ⟨hp2_max, hp3_max, hp3'_max, hp2_bot, hp3_bot, hp3'_bot, h23, h23', h33'⟩

/-- Non-principality of `p2` in `Ideal (Zsqrtd (-5))`, derived from
`zsqrtdNeg5_evanston_lec8_nonunique_factorization` (absence of norm-`2` elements). -/
lemma p2_not_principal : ¬ ∃ α : Zsqrtd (-5), p2 = Ideal.span {α} := by
  rintro ⟨α, hα⟩
  have h2_mem : (2 : Zsqrtd (-5)) ∈ Ideal.span {α} := hα ▸ Ideal.subset_span (by simp)
  have h1p_mem : (⟨1, 1⟩ : Zsqrtd (-5)) ∈ Ideal.span {α} :=
    hα ▸ Ideal.subset_span (by simp)
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton.mp h2_mem
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton.mp h1p_mem
  have hnorm2 : α.norm * u.norm = 4 := by
    rw [← Zsqrtd.norm_mul, ← hu]
    decide
  have hnorm6 : α.norm * v.norm = 6 := by
    rw [← Zsqrtd.norm_mul, ← hv]
    decide
  have hα_nn : 0 ≤ α.norm := Zsqrtd.norm_nonneg (by norm_num) α
  have hdiv2 : α.norm ∣ 2 := by
    refine ⟨v.norm - u.norm, ?_⟩
    linarith
  have hle2 : α.norm ≤ 2 := Int.le_of_dvd (by norm_num) hdiv2
  have hno2 := (zsqrtdNeg5_evanston_lec8_nonunique_factorization.2.2.1 α).1
  have hα_pos : α.norm ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hnorm2
    norm_num at hnorm2
  have hα1 : α.norm = 1 := by omega
  have hunit : IsUnit α := (zsqrtdNeg5_isUnit_iff_and_no_norm_two_three α).1.mpr
    (zsqrtdNeg5_evanston_lec8_nonunique_factorization.2.1 α |>.mp hα1)
  have htop : p2 = ⊤ := hα.trans (Ideal.span_singleton_eq_top.mpr hunit)
  exact p2_p3_p3'_maximal_ne_bot_pairwise_ne.1.ne_top htop

/-- Non-principality of `p3` and `p3'` in `Ideal (Zsqrtd (-5))`, derived from
`zsqrtdNeg5_evanston_lec8_nonunique_factorization` (absence of norm-`3` elements). -/
lemma p3_and_p3'_not_principal :
    (¬ ∃ α : Zsqrtd (-5), p3 = Ideal.span {α}) ∧
    (¬ ∃ α : Zsqrtd (-5), p3' = Ideal.span {α}) := by
  constructor
  · rintro ⟨α, hα⟩
    have h3_mem : (3 : Zsqrtd (-5)) ∈ Ideal.span {α} := hα ▸ Ideal.subset_span (by simp)
    have h1p_mem : (⟨1, 1⟩ : Zsqrtd (-5)) ∈ Ideal.span {α} :=
      hα ▸ Ideal.subset_span (by simp)
    obtain ⟨u, hu⟩ := Ideal.mem_span_singleton.mp h3_mem
    obtain ⟨v, hv⟩ := Ideal.mem_span_singleton.mp h1p_mem
    have hnorm9 : α.norm * u.norm = 9 := by
      rw [← Zsqrtd.norm_mul, ← hu]
      decide
    have hnorm6 : α.norm * v.norm = 6 := by
      rw [← Zsqrtd.norm_mul, ← hv]
      decide
    have hα_nn : 0 ≤ α.norm := Zsqrtd.norm_nonneg (by norm_num) α
    have hdiv3 : α.norm ∣ 3 := by
      refine ⟨u.norm - v.norm, ?_⟩
      linarith
    have hle3 : α.norm ≤ 3 := Int.le_of_dvd (by norm_num) hdiv3
    have ⟨hno2, hno3⟩ := zsqrtdNeg5_evanston_lec8_nonunique_factorization.2.2.1 α
    have hα_pos : α.norm ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hnorm9
      norm_num at hnorm9
    have hα1 : α.norm = 1 := by omega
    have hunit : IsUnit α := (zsqrtdNeg5_isUnit_iff_and_no_norm_two_three α).1.mpr
      (zsqrtdNeg5_evanston_lec8_nonunique_factorization.2.1 α |>.mp hα1)
    have htop : p3 = ⊤ := hα.trans (Ideal.span_singleton_eq_top.mpr hunit)
    exact p2_p3_p3'_maximal_ne_bot_pairwise_ne.2.1.ne_top htop
  · rintro ⟨α, hα⟩
    have h3_mem : (3 : Zsqrtd (-5)) ∈ Ideal.span {α} := hα ▸ Ideal.subset_span (by simp)
    have h1m_mem : (⟨1, -1⟩ : Zsqrtd (-5)) ∈ Ideal.span {α} :=
      hα ▸ Ideal.subset_span (by simp)
    obtain ⟨u, hu⟩ := Ideal.mem_span_singleton.mp h3_mem
    obtain ⟨v, hv⟩ := Ideal.mem_span_singleton.mp h1m_mem
    have hnorm9 : α.norm * u.norm = 9 := by
      rw [← Zsqrtd.norm_mul, ← hu]
      decide
    have hnorm6 : α.norm * v.norm = 6 := by
      rw [← Zsqrtd.norm_mul, ← hv]
      decide
    have hα_nn : 0 ≤ α.norm := Zsqrtd.norm_nonneg (by norm_num) α
    have hdiv3 : α.norm ∣ 3 := by
      refine ⟨u.norm - v.norm, ?_⟩
      linarith
    have hle3 : α.norm ≤ 3 := Int.le_of_dvd (by norm_num) hdiv3
    have ⟨hno2, hno3⟩ := zsqrtdNeg5_evanston_lec8_nonunique_factorization.2.2.1 α
    have hα_pos : α.norm ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hnorm9
      norm_num at hnorm9
    have hα1 : α.norm = 1 := by omega
    have hunit : IsUnit α := (zsqrtdNeg5_isUnit_iff_and_no_norm_two_three α).1.mpr
      (zsqrtdNeg5_evanston_lec8_nonunique_factorization.2.1 α |>.mp hα1)
    have htop : p3' = ⊤ := hα.trans (Ideal.span_singleton_eq_top.mpr hunit)
    exact p2_p3_p3'_maximal_ne_bot_pairwise_ne.2.2.1.ne_top htop

/-! ### 3. `HeightOneSpectrum (𝓞 K)` Transport and Concrete `ℚ(√-5)` Euler Product -/

/-- Pullback of a nonzero prime ideal `P` of `Zsqrtd (-5)` along `e : 𝓞 K ≃+* Zsqrtd (-5)`
to `HeightOneSpectrum (𝓞 K)`. -/
def toHeightOneSpectrum {K : Type*} [Field K] [NumberField K]
    (e : 𝓞 K ≃+* Zsqrtd (-5)) (P : Ideal (Zsqrtd (-5)))
    (hP : P.IsPrime) (hne : P ≠ ⊥) : HeightOneSpectrum (𝓞 K) where
  asIdeal := P.comap e.toRingHom
  isPrime := P.comap_isPrime e.toRingHom
  ne_bot := (Ideal.eq_bot_of_comap_eq_bot' e.surjective).mt hne

/-- The height-one prime above `2` in `𝓞 K` induced by `e : 𝓞 K ≃+* Zsqrtd (-5)`. -/
def place2 {K : Type*} [Field K] [NumberField K] (e : 𝓞 K ≃+* Zsqrtd (-5)) :
    HeightOneSpectrum (𝓞 K) :=
  toHeightOneSpectrum e p2
    p2_p3_p3'_maximal_ne_bot_pairwise_ne.1.isPrime
    p2_p3_p3'_maximal_ne_bot_pairwise_ne.2.2.2.1

/-- The height-one prime `p₃` above `3` in `𝓞 K` induced by `e : 𝓞 K ≃+* Zsqrtd (-5)`. -/
def place3 {K : Type*} [Field K] [NumberField K] (e : 𝓞 K ≃+* Zsqrtd (-5)) :
    HeightOneSpectrum (𝓞 K) :=
  toHeightOneSpectrum e p3
    p2_p3_p3'_maximal_ne_bot_pairwise_ne.2.1.isPrime
    p2_p3_p3'_maximal_ne_bot_pairwise_ne.2.2.2.2.1

/-- The conjugate height-one prime `p₃'` above `3` in `𝓞 K` induced by `e`. -/
def place3' {K : Type*} [Field K] [NumberField K] (e : 𝓞 K ≃+* Zsqrtd (-5)) :
    HeightOneSpectrum (𝓞 K) :=
  toHeightOneSpectrum e p3'
    p2_p3_p3'_maximal_ne_bot_pairwise_ne.2.2.1.isPrime
    p2_p3_p3'_maximal_ne_bot_pairwise_ne.2.2.2.2.2.1

private def comap_quotient_equiv {K : Type*} [Field K] [NumberField K]
    (e : 𝓞 K ≃+* Zsqrtd (-5)) (P : Ideal (Zsqrtd (-5))) :
    (𝓞 K ⧸ P.comap e.toRingHom) ≃+* (Zsqrtd (-5) ⧸ P) := by
  let f : 𝓞 K →+* (Zsqrtd (-5) ⧸ P) := (Ideal.Quotient.mk P).comp e.toRingHom
  have hf_surj : Function.Surjective f := Ideal.Quotient.mk_surjective.comp e.surjective
  have hker : RingHom.ker f = P.comap e.toRingHom := by
    ext x
    simp [f, RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]
  exact (Ideal.quotEquivOfEq hker.symm).trans
    (RingHom.quotientKerEquivOfSurjective hf_surj)

/-- Absolute norm computation, pairwise distinctness, ideal identities, and
non-principality for `place2 e`, `place3 e`, `place3' e` in `𝓞 K`. -/
lemma places_absNorm_distinct_identities_and_nonprincipal
    {K : Type*} [Field K] [NumberField K] (e : 𝓞 K ≃+* Zsqrtd (-5)) :
    (place2 e).asIdeal.absNorm = 2 ∧
    (place3 e).asIdeal.absNorm = 3 ∧
    (place3' e).asIdeal.absNorm = 3 ∧
    place2 e ≠ place3 e ∧
    place2 e ≠ place3' e ∧
    place3 e ≠ place3' e ∧
    (place2 e).asIdeal ^ 2 = Ideal.span {(2 : 𝓞 K)} ∧
    (place3 e).asIdeal * (place3' e).asIdeal = Ideal.span {(3 : 𝓞 K)} ∧
    (place2 e).asIdeal * (place3 e).asIdeal = Ideal.span {e.symm ⟨1, 1⟩} ∧
    (place2 e).asIdeal * (place3' e).asIdeal = Ideal.span {e.symm ⟨1, -1⟩} ∧
    (¬ ∃ α : 𝓞 K, (place2 e).asIdeal = Ideal.span {α}) ∧
    (¬ ∃ α : 𝓞 K, (place3 e).asIdeal = Ideal.span {α}) ∧
    (¬ ∃ α : 𝓞 K, (place3' e).asIdeal = Ideal.span {α}) := by
  have hnorm2 : (place2 e).asIdeal.absNorm = 2 := by
    have heq : (𝓞 K ⧸ (place2 e).asIdeal) ≃+* ZMod 2 :=
      (comap_quotient_equiv e p2).trans p2QuotientEquivZMod2
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_congr heq.toEquiv,
      Nat.card_eq_fintype_card, ZMod.card]
  have hnorm3 : (place3 e).asIdeal.absNorm = 3 := by
    have heq : (𝓞 K ⧸ (place3 e).asIdeal) ≃+* ZMod 3 :=
      (comap_quotient_equiv e p3).trans p3QuotientEquivZMod3
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_congr heq.toEquiv,
      Nat.card_eq_fintype_card, ZMod.card]
  have hnorm3' : (place3' e).asIdeal.absNorm = 3 := by
    have heq : (𝓞 K ⧸ (place3' e).asIdeal) ≃+* ZMod 3 :=
      (comap_quotient_equiv e p3').trans p3'QuotientEquivZMod3
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_congr heq.toEquiv,
      Nat.card_eq_fintype_card, ZMod.card]
  have hinj := Ideal.comap_injective_of_surjective e.toRingHom e.surjective
  have hne23 : place2 e ≠ place3 e := fun h =>
    p2_p3_p3'_maximal_ne_bot_pairwise_ne.2.2.2.2.2.2.1
      (hinj (congrArg HeightOneSpectrum.asIdeal h))
  have hne23' : place2 e ≠ place3' e := fun h =>
    p2_p3_p3'_maximal_ne_bot_pairwise_ne.2.2.2.2.2.2.2.1
      (hinj (congrArg HeightOneSpectrum.asIdeal h))
  have hne33' : place3 e ≠ place3' e := fun h =>
    p2_p3_p3'_maximal_ne_bot_pairwise_ne.2.2.2.2.2.2.2.2
      (hinj (congrArg HeightOneSpectrum.asIdeal h))
  have hcomap_map : ∀ P : Ideal (Zsqrtd (-5)),
      P.comap e.toRingHom = P.map e.symm.toRingHom := by
    intro P
    ext x
    simp only [Ideal.mem_comap, RingEquiv.toRingHom_eq_coe]
    constructor
    · intro hx
      have : x = e.symm (e x) := (e.symm_apply_apply x).symm
      rw [this]
      exact Ideal.mem_map_of_mem e.symm.toRingHom hx
    · intro hx
      have hsub : P.map e.symm.toRingHom ≤ P.comap e.toRingHom := by
        rw [Ideal.map_le_iff_le_comap]
        intro y hy
        rw [Ideal.mem_comap]
        change e (e.symm y) ∈ P
        rwa [e.apply_symm_apply]
      exact hsub hx
  have hmap_span : ∀ a : Zsqrtd (-5),
      (Ideal.span {a}).map e.symm.toRingHom = Ideal.span {e.symm a} := by
    intro a
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  have hid2 : (place2 e).asIdeal ^ 2 = Ideal.span {(2 : 𝓞 K)} := by
    change (p2.comap e.toRingHom) ^ 2 = _
    rw [hcomap_map p2, ← Ideal.map_pow, p2_sq_eq_span_two, hmap_span, map_ofNat]
  have hid3 : (place3 e).asIdeal * (place3' e).asIdeal = Ideal.span {(3 : 𝓞 K)} := by
    change p3.comap e.toRingHom * p3'.comap e.toRingHom = _
    rw [hcomap_map p3, hcomap_map p3', ← Ideal.map_mul, p3_mul_p3'_eq_span_three, hmap_span,
      map_ofNat]
  have hid23 : (place2 e).asIdeal * (place3 e).asIdeal = Ideal.span {e.symm ⟨1, 1⟩} := by
    change p2.comap e.toRingHom * p3.comap e.toRingHom = _
    rw [hcomap_map p2, hcomap_map p3, ← Ideal.map_mul, p2_mul_p3_eq_span, hmap_span]
  have hid23' : (place2 e).asIdeal * (place3' e).asIdeal = Ideal.span {e.symm ⟨1, -1⟩} := by
    change p2.comap e.toRingHom * p3'.comap e.toRingHom = _
    rw [hcomap_map p2, hcomap_map p3', ← Ideal.map_mul, p2_mul_p3'_eq_span, hmap_span]
  have hnp_transport : ∀ (P : Ideal (Zsqrtd (-5))),
      (¬ ∃ α : Zsqrtd (-5), P = Ideal.span {α}) →
      ¬ ∃ β : 𝓞 K, P.comap e.toRingHom = Ideal.span {β} := by
    intro P hP ⟨β, hβ⟩
    apply hP
    refine ⟨e β, ?_⟩
    have hmap : (P.comap e.toRingHom).map e.toRingHom = P := by
      rw [hcomap_map P, Ideal.map_map]
      have heq : (e.toRingHom.comp e.symm.toRingHom) = RingHom.id _ := by
        apply RingHom.ext
        intro x
        simp
      rw [heq, Ideal.map_id]
    rw [← hmap, hβ, Ideal.map_span, Set.image_singleton]
    rfl
  exact ⟨hnorm2, hnorm3, hnorm3', hne23, hne23', hne33',
    hid2, hid3, hid23, hid23',
    hnp_transport p2 p2_not_principal,
    hnp_transport p3 p3_and_p3'_not_principal.1,
    hnp_transport p3' p3_and_p3'_not_principal.2⟩

/-- Dedekind zeta and trivial Hecke Euler-product bridge for any number field `K`
whose ring of integers is isomorphic to `Zsqrtd (-5)`, exposing the local Euler
factors at `place2 e`, `place3 e`, and `place3' e`. -/
lemma numberField_zsqrtdNeg5_dedekindZeta_and_hecke_bridge
    {K : Type*} [Field K] [NumberField K] (e : 𝓞 K ≃+* Zsqrtd (-5))
    {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun v : HeightOneSpectrum (𝓞 K) ↦
      (1 - (v.asIdeal.absNorm : ℂ) ^ (-s))⁻¹) (dedekindZeta K s) ∧
    (1 : HeckeCharacter (𝓞 K) K).LSeries s = dedekindZeta K s ∧
    (1 - ((place2 e).asIdeal.absNorm : ℂ) ^ (-s))⁻¹ = (1 - (2 : ℂ) ^ (-s))⁻¹ ∧
    (1 - ((place3 e).asIdeal.absNorm : ℂ) ^ (-s))⁻¹ = (1 - (3 : ℂ) ^ (-s))⁻¹ ∧
    (1 - ((place3' e).asIdeal.absNorm : ℂ) ^ (-s))⁻¹ = (1 - (3 : ℂ) ^ (-s))⁻¹ := by
  have h := places_absNorm_distinct_identities_and_nonprincipal e
  refine ⟨dedekindZeta_hasProd K hs, heckeLSeries_one_eq_dedekindZeta hs, ?_, ?_, ?_⟩
  · rw [h.1]; norm_num
  · rw [h.2.1]; norm_num
  · rw [h.2.2.1]; norm_num

/-- Irreducibility of `X ^ 2 + C 5` over `ℚ`. -/
lemma irreducible_X_sq_add_five : Irreducible (X ^ 2 + C (5 : ℚ) : ℚ[X]) := by
  refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot ?_ ?_
  · rw [Polynomial.natDegree_X_pow_add_C]
    norm_num
  · intro r hr
    rw [Polynomial.IsRoot.def, Polynomial.eval_add, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C] at hr
    nlinarith [sq_nonneg r]

/-- Scoped `Fact` instance providing `NumberField (AdjoinRoot (X ^ 2 + C 5 : ℚ[X]))`. -/
scoped instance instFactIrreducibleXSqAddFive :
    Fact (Irreducible (X ^ 2 + C (5 : ℚ) : ℚ[X])) :=
  ⟨irreducible_X_sq_add_five⟩

/-- Concrete field `ℚ(√-5) := ℚ[X] / (X² + 5)`. -/
abbrev QSqrtNeg5 := AdjoinRoot (X ^ 2 + C (5 : ℚ) : ℚ[X])

/-- Canonical generator `√-5` in `QSqrtNeg5`. -/
def sqrtNeg5Gen : QSqrtNeg5 :=
  AdjoinRoot.root (X ^ 2 + C (5 : ℚ) : ℚ[X])

lemma sqrtNeg5Gen_sq : sqrtNeg5Gen * sqrtNeg5Gen = ((-5 : ℤ) : QSqrtNeg5) := by
  have hroot := AdjoinRoot.eval₂_root (X ^ 2 + C (5 : ℚ) : ℚ[X])
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_C] at hroot
  have hadd : sqrtNeg5Gen * sqrtNeg5Gen + (5 : QSqrtNeg5) = 0 := by
    simpa [sqrtNeg5Gen, sq] using hroot
  have hm5 : ((-5 : ℤ) : QSqrtNeg5) = -(5 : QSqrtNeg5) := by norm_num
  rw [hm5]
  exact eq_neg_of_add_eq_zero_left hadd

/-- Canonical ring homomorphism `Zsqrtd (-5) →+* QSqrtNeg5`. -/
def zsqrtdNeg5ToQSqrtNeg5 : Zsqrtd (-5) →+* QSqrtNeg5 :=
  Zsqrtd.lift ⟨sqrtNeg5Gen, sqrtNeg5Gen_sq⟩

/-- Scoped `Algebra (Zsqrtd (-5)) QSqrtNeg5` instance. -/
scoped instance instAlgebraZsqrtdNeg5QSqrtNeg5 : Algebra (Zsqrtd (-5)) QSqrtNeg5 :=
  RingHom.toAlgebra zsqrtdNeg5ToQSqrtNeg5

/-- Scoped scalar tower `ℤ → Zsqrtd (-5) → QSqrtNeg5`. -/
scoped instance instIsScalarTowerIntZsqrtdNeg5QSqrtNeg5 :
    IsScalarTower ℤ (Zsqrtd (-5)) QSqrtNeg5 :=
  IsScalarTower.of_algebraMap_eq' (by
    ext n
    simp)

private lemma qSqrtNeg5_rat_decomp (x : QSqrtNeg5) :
    ∃ a b : ℚ, x = algebraMap ℚ QSqrtNeg5 a + algebraMap ℚ QSqrtNeg5 b * sqrtNeg5Gen := by
  have hp : (X ^ 2 + C (5 : ℚ) : ℚ[X]) ≠ 0 := irreducible_X_sq_add_five.ne_zero
  let pb := AdjoinRoot.powerBasis hp
  have hdim : pb.dim = 2 := by
    rw [AdjoinRoot.powerBasis_dim, Polynomial.natDegree_X_pow_add_C]
  have hsum := pb.basis.sum_repr x
  have h0 : 0 < pb.dim := by rw [hdim]; norm_num
  have h1 : 1 < pb.dim := by rw [hdim]; norm_num
  let i0 : Fin pb.dim := ⟨0, h0⟩
  let i1 : Fin pb.dim := ⟨1, h1⟩
  refine ⟨pb.basis.repr x i0, pb.basis.repr x i1, ?_⟩
  have hfin : (Finset.univ : Finset (Fin pb.dim)) = {i0, i1} := by
    ext j
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    rcases j with ⟨k, hk⟩
    rw [hdim] at hk
    interval_cases k
    · left; exact Fin.ext rfl
    · right; exact Fin.ext rfl
  have hb0 : pb.basis i0 = 1 := by
    rw [pb.basis_eq_pow]
    simp [i0]
  have hb1 : pb.basis i1 = sqrtNeg5Gen := by
    rw [pb.basis_eq_pow]
    simp [i1, pb, AdjoinRoot.powerBasis_gen, sqrtNeg5Gen]
  calc x
    _ = ∑ i, (pb.basis.repr x) i • pb.basis i := hsum.symm
    _ = (pb.basis.repr x) i0 • pb.basis i0 + (pb.basis.repr x) i1 • pb.basis i1 := by
        rw [hfin, Finset.sum_pair (by intro h; have := congrArg Fin.val h; norm_num at this)]
    _ = algebraMap ℚ QSqrtNeg5 (pb.basis.repr x i0) +
          algebraMap ℚ QSqrtNeg5 (pb.basis.repr x i1) * sqrtNeg5Gen := by
        rw [hb0, hb1, Algebra.smul_def, Algebra.smul_def, mul_one]
        rfl

/-- Scoped `IsIntegralClosure (Zsqrtd (-5)) ℤ QSqrtNeg5` proving `ℤ[√-5]` is the
full ring of integers of `ℚ(√-5)` (since `-5 % 4 = 3`). -/
scoped instance instIsIntegralClosureZsqrtdNeg5 :
    IsIntegralClosure (Zsqrtd (-5)) ℤ QSqrtNeg5 where
  algebraMap_injective := Zsqrtd.lift_injective ⟨sqrtNeg5Gen, sqrtNeg5Gen_sq⟩
    (fun n hn => by nlinarith)
  isIntegral_iff {x} := by
    constructor
    · intro hx
      obtain ⟨a, b, rfl⟩ := qSqrtNeg5_rat_decomp x
      by_cases hb : b = 0
      · subst hb
        rw [map_zero, zero_mul, add_zero] at hx ⊢
        have ha_int : IsIntegral ℤ a := by
          obtain ⟨P, hPmon, hPev⟩ := hx
          refine ⟨P, hPmon, ?_⟩
          apply (algebraMap ℚ QSqrtNeg5).injective
          have hae : Polynomial.eval₂ (algebraMap ℤ QSqrtNeg5) (algebraMap ℚ QSqrtNeg5 a) P =
              algebraMap ℚ QSqrtNeg5 (Polynomial.eval₂ (algebraMap ℤ ℚ) a P) := by
            rw [Polynomial.hom_eval₂]
            congr 1
          rw [map_zero, ← hae]
          exact hPev
        obtain ⟨m, rfl⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).mp ha_int
        refine ⟨⟨m, 0⟩, ?_⟩
        change zsqrtdNeg5ToQSqrtNeg5 ⟨m, 0⟩ = algebraMap ℚ QSqrtNeg5 (m : ℚ)
        simp [zsqrtdNeg5ToQSqrtNeg5]
      · set x0 : QSqrtNeg5 :=
            algebraMap ℚ QSqrtNeg5 a + algebraMap ℚ QSqrtNeg5 b * sqrtNeg5Gen
        have hnot_rat : ∀ r : ℚ, x0 ≠ algebraMap ℚ QSqrtNeg5 r := by
          intro r hr
          have h1 : algebraMap ℚ QSqrtNeg5 b * sqrtNeg5Gen =
              algebraMap ℚ QSqrtNeg5 (r - a) := by
            rw [map_sub]
            linear_combination hr
          have hsq := congrArg (fun z : QSqrtNeg5 => z * z) h1
          have hm5 : algebraMap ℚ QSqrtNeg5 (-5 : ℚ) = ((-5 : ℤ) : QSqrtNeg5) := by
            norm_num
          have hsq' : algebraMap ℚ QSqrtNeg5 (b ^ 2 * (-5)) =
              algebraMap ℚ QSqrtNeg5 ((r - a) ^ 2) := by
            calc algebraMap ℚ QSqrtNeg5 (b ^ 2 * (-5))
              _ = algebraMap ℚ QSqrtNeg5 b * algebraMap ℚ QSqrtNeg5 b *
                    ((-5 : ℤ) : QSqrtNeg5) := by
                  rw [← hm5]
                  simp only [map_mul, map_pow]
                  ring
              _ = (algebraMap ℚ QSqrtNeg5 b * sqrtNeg5Gen) *
                    (algebraMap ℚ QSqrtNeg5 b * sqrtNeg5Gen) := by
                  rw [← sqrtNeg5Gen_sq]; ring
              _ = algebraMap ℚ QSqrtNeg5 (r - a) * algebraMap ℚ QSqrtNeg5 (r - a) := hsq
              _ = algebraMap ℚ QSqrtNeg5 ((r - a) ^ 2) := by
                  simp only [map_mul, sq]
          have hrat := (algebraMap ℚ QSqrtNeg5).injective hsq'
          have hneg : b ^ 2 * (-5 : ℚ) < 0 :=
            mul_neg_of_pos_of_neg (sq_pos_iff.mpr hb) (by norm_num)
          nlinarith [sq_nonneg (r - a)]
        let q : ℚ[X] := X ^ 2 - C (2 * a) * X + C (a ^ 2 + 5 * b ^ 2)
        have hq_monic : q.Monic := by
          dsimp [q]
          monicity!
        have hq_deg : q.natDegree = 2 := by
          dsimp [q]
          compute_degree!
        have hq_eval : Polynomial.aeval x0 q = 0 := by
          dsimp [q, x0]
          simp only [map_add, map_sub, map_mul, map_pow, Polynomial.aeval_X,
            Polynomial.aeval_C, map_ofNat]
          have hsq : sqrtNeg5Gen ^ 2 = -5 := by
            rw [sq, sqrtNeg5Gen_sq]
            norm_num
          linear_combination (algebraMap ℚ QSqrtNeg5 b) ^ 2 * hsq
        have hmin_dvd : minpoly ℚ x0 ∣ q :=
          minpoly.dvd ℚ x0 hq_eval
        have hmin_int : IsIntegral ℚ x0 :=
          ⟨q, hq_monic, hq_eval⟩
        have hmin_pos : 0 < (minpoly ℚ x0).natDegree :=
          minpoly.natDegree_pos hmin_int
        have hmin_le : (minpoly ℚ x0).natDegree ≤ 2 := by
          have hle_deg := Polynomial.natDegree_le_of_dvd hmin_dvd hq_monic.ne_zero
          omega
        have hmin_ne1 : (minpoly ℚ x0).natDegree ≠ 1 := by
          intro h1
          have hlin := (minpoly.monic hmin_int).eq_X_add_C h1
          have hae := minpoly.aeval ℚ x0
          rw [hlin, map_add, Polynomial.aeval_X, Polynomial.aeval_C] at hae
          exact hnot_rat (-((minpoly ℚ x0).coeff 0)) (by
            rw [map_neg]
            linear_combination hae)
        have hmin_deg2 : (minpoly ℚ x0).natDegree = 2 := by
          omega
        have hmin_eq : minpoly ℚ x0 = q :=
          (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hmin_int) hq_monic
            hmin_dvd (by omega)).symm
        have hcoeff := minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hx
        rw [hmin_eq] at hcoeff
        have hc1 : q.coeff 1 = (((minpoly ℤ x0).coeff 1 : ℤ) : ℚ) := by
          rw [hcoeff, Polynomial.coeff_map]
          rfl
        have hc0 : q.coeff 0 = (((minpoly ℤ x0).coeff 0 : ℤ) : ℚ) := by
          rw [hcoeff, Polynomial.coeff_map]
          rfl
        have hq1 : q.coeff 1 = -(2 * a) := by
          dsimp [q]
          simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_X_pow,
            Polynomial.coeff_C_mul_X, Polynomial.coeff_C]
          norm_num
        have hq0 : q.coeff 0 = a ^ 2 + 5 * b ^ 2 := by
          dsimp [q]
          simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_X_pow,
            Polynomial.coeff_C_mul_X, Polynomial.coeff_C]
          norm_num
        set m : ℤ := -((minpoly ℤ x0).coeff 1)
        set n : ℤ := (minpoly ℤ x0).coeff 0
        have hm : 2 * a = (m : ℚ) := by
          dsimp [m]
          rw [← hc1, hq1, neg_neg]
        have hn : a ^ 2 + 5 * b ^ 2 = (n : ℚ) := by
          dsimp [n]
          rw [← hc0, hq0]
        have h5b : 5 * (2 * b) ^ 2 = ((4 * n - m ^ 2 : ℤ) : ℚ) := by
          push_cast
          rw [← hm, ← hn]
          ring
        obtain ⟨r, hr_def⟩ : ∃ r : ℚ, r = 2 * b := ⟨2 * b, rfl⟩
        have hr_5 : 5 * r ^ 2 = ((4 * n - m ^ 2 : ℤ) : ℚ) := by
          rw [hr_def, h5b]
        have hr_num : (5 : ℤ) * r.num ^ 2 = (4 * n - m ^ 2) * (r.den : ℤ) ^ 2 := by
          have hr_eq : (r.num : ℚ) / (r.den : ℚ) = r := Rat.num_div_den r
          have hden0 : (r.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr r.den_nz
          have hr_mul : (r.num : ℚ) = r * (r.den : ℚ) := by
            rw [← div_mul_cancel₀ (r.num : ℚ) hden0, hr_eq]
          have hq_eq : ((5 * r.num ^ 2 : ℤ) : ℚ) =
              (((4 * n - m ^ 2) * (r.den : ℤ) ^ 2 : ℤ) : ℚ) := by
            calc ((5 * r.num ^ 2 : ℤ) : ℚ)
              _ = 5 * (r.num : ℚ) ^ 2 := by push_cast; ring
              _ = 5 * (r * (r.den : ℚ)) ^ 2 := by rw [hr_mul]
              _ = (5 * r ^ 2) * (r.den : ℚ) ^ 2 := by ring
              _ = ((4 * n - m ^ 2 : ℤ) : ℚ) * (r.den : ℚ) ^ 2 := by rw [hr_5]
              _ = (((4 * n - m ^ 2) * (r.den : ℤ) ^ 2 : ℤ) : ℚ) := by push_cast; ring
          exact Int.cast_injective hq_eq
        have hdvd5 : r.den ^ 2 ∣ 5 := by
          have hnat : 5 * r.num.natAbs ^ 2 = (4 * n - m ^ 2).natAbs * r.den ^ 2 := by
            have ha := congrArg Int.natAbs hr_num
            simpa [Int.natAbs_mul, Int.natAbs_pow] using ha
          have hmul_dvd : r.den ^ 2 ∣ 5 * r.num.natAbs ^ 2 :=
            ⟨(4 * n - m ^ 2).natAbs, by linarith⟩
          exact (r.reduced.symm.pow 2 2).dvd_of_dvd_mul_right hmul_dvd
        have hden_le : r.den ^ 2 ≤ 5 := Nat.le_of_dvd (by norm_num) hdvd5
        have hden1 : r.den = 1 := by
          have hne0 : r.den ≠ 0 := r.den_nz
          have hle2 : r.den ≤ 2 := by nlinarith
          interval_cases hden : r.den
          · contradiction
          · rfl
          · exfalso
            norm_num at hdvd5
        set k : ℤ := r.num
        have hk : 2 * b = (k : ℚ) := by
          rw [← hr_def]
          calc r = (r.num : ℚ) / (r.den : ℚ) := (Rat.num_div_den r).symm
            _ = (k : ℚ) := by rw [hden1]; simp [k]
        have hmod : m ^ 2 + 5 * k ^ 2 = 4 * n := by
          have hq : ((m ^ 2 + 5 * k ^ 2 : ℤ) : ℚ) = ((4 * n : ℤ) : ℚ) := by
            push_cast
            rw [← hm, ← hk]
            linarith [hn]
          exact Int.cast_injective hq
        have heven_m : 2 ∣ m := by
          rcases Int.emod_two_eq_zero_or_one m with hm0 | hm1 <;>
            rcases Int.emod_two_eq_zero_or_one k with hk0 | hk1
          · exact Int.dvd_of_emod_eq_zero hm0
          · exfalso
            obtain ⟨q1, hq1_eq⟩ := Int.dvd_of_emod_eq_zero hm0
            have hk_eq : k = 2 * (k / 2) + 1 := by omega
            have hlin : 4 * (q1 ^ 2 + 5 * (k / 2) ^ 2 + 5 * (k / 2) + 1) + 1 = 4 * n := by
              calc 4 * (q1 ^ 2 + 5 * (k / 2) ^ 2 + 5 * (k / 2) + 1) + 1
                _ = (2 * q1) ^ 2 + 5 * (2 * (k / 2) + 1) ^ 2 := by ring
                _ = m ^ 2 + 5 * k ^ 2 := by rw [← hq1_eq, ← hk_eq]
                _ = 4 * n := hmod
            omega
          · exfalso
            obtain ⟨q2, hq2_eq⟩ := Int.dvd_of_emod_eq_zero hk0
            have hm_eq : m = 2 * (m / 2) + 1 := by omega
            have hlin : 4 * ((m / 2) ^ 2 + (m / 2) + 5 * q2 ^ 2) + 1 = 4 * n := by
              calc 4 * ((m / 2) ^ 2 + (m / 2) + 5 * q2 ^ 2) + 1
                _ = (2 * (m / 2) + 1) ^ 2 + 5 * (2 * q2) ^ 2 := by ring
                _ = m ^ 2 + 5 * k ^ 2 := by rw [← hm_eq, ← hq2_eq]
                _ = 4 * n := hmod
            omega
          · exfalso
            have hm_eq : m = 2 * (m / 2) + 1 := by omega
            have hk_eq : k = 2 * (k / 2) + 1 := by omega
            have hlin : 4 * ((m / 2) ^ 2 + (m / 2) + 5 * (k / 2) ^ 2 +
                5 * (k / 2) + 1) + 2 = 4 * n := by
              calc 4 * ((m / 2) ^ 2 + (m / 2) + 5 * (k / 2) ^ 2 +
                    5 * (k / 2) + 1) + 2
                _ = (2 * (m / 2) + 1) ^ 2 + 5 * (2 * (k / 2) + 1) ^ 2 := by ring
                _ = m ^ 2 + 5 * k ^ 2 := by rw [← hm_eq, ← hk_eq]
                _ = 4 * n := hmod
            omega
        have heven_k : 2 ∣ k := by
          rcases Int.emod_two_eq_zero_or_one k with hk0 | hk1
          · exact Int.dvd_of_emod_eq_zero hk0
          · exfalso
            obtain ⟨q1, hq1_eq⟩ := heven_m
            have hk_eq : k = 2 * (k / 2) + 1 := by omega
            have hlin : 4 * (q1 ^ 2 + 5 * (k / 2) ^ 2 + 5 * (k / 2) + 1) + 1 = 4 * n := by
              calc 4 * (q1 ^ 2 + 5 * (k / 2) ^ 2 + 5 * (k / 2) + 1) + 1
                _ = (2 * q1) ^ 2 + 5 * (2 * (k / 2) + 1) ^ 2 := by ring
                _ = m ^ 2 + 5 * k ^ 2 := by rw [← hq1_eq, ← hk_eq]
                _ = 4 * n := hmod
            omega
        obtain ⟨a0, ha0⟩ := heven_m
        obtain ⟨b0, hb0⟩ := heven_k
        refine ⟨⟨a0, b0⟩, ?_⟩
        have ha_eq : a = (a0 : ℚ) := by
          have : 2 * a = 2 * (a0 : ℚ) := by rw [hm, ha0]; push_cast; ring
          linarith
        have hb_eq : b = (b0 : ℚ) := by
          have : 2 * b = 2 * (b0 : ℚ) := by rw [hk, hb0]; push_cast; ring
          linarith
        change zsqrtdNeg5ToQSqrtNeg5 ⟨a0, b0⟩ = x0
        dsimp [x0]
        rw [ha_eq, hb_eq]
        simp [zsqrtdNeg5ToQSqrtNeg5]
    · rintro ⟨⟨a, b⟩, rfl⟩
      have hgen : IsIntegral ℤ sqrtNeg5Gen := by
        refine ⟨X ^ 2 + C 5, by monicity!, ?_⟩
        simp only [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, map_ofNat]
        have h5ev : Polynomial.eval₂ (algebraMap ℤ QSqrtNeg5) sqrtNeg5Gen 5 = (5 : QSqrtNeg5) := by
          simp
        have hsq_gen : sqrtNeg5Gen ^ 2 = (-5 : QSqrtNeg5) := by
          rw [pow_two, sqrtNeg5Gen_sq]
          norm_num
        rw [h5ev, hsq_gen]
        norm_num
      change IsIntegral ℤ (zsqrtdNeg5ToQSqrtNeg5 ⟨a, b⟩)
      simp only [zsqrtdNeg5ToQSqrtNeg5, Zsqrtd.lift_apply_apply]
      exact (isIntegral_intCast a).add ((isIntegral_intCast b).mul hgen)

/-- Concrete ring isomorphism `𝓞 QSqrtNeg5 ≃+* Zsqrtd (-5)`. -/
def ringOfIntegersEquivZsqrtdNeg5 : 𝓞 QSqrtNeg5 ≃+* Zsqrtd (-5) :=
  @NumberField.RingOfIntegers.equiv QSqrtNeg5 _ (Zsqrtd (-5)) _
    instAlgebraZsqrtdNeg5QSqrtNeg5 instIsIntegralClosureZsqrtdNeg5

/-- Concrete height-one places `place2`, `place3`, `place3'` on `𝓞 QSqrtNeg5`
together with `dedekindZeta_hasProd` and `heckeLSeries_one_eq_dedekindZeta`. -/
lemma qSqrtNeg5_places_and_dedekindZeta_bridge {s : ℂ} (hs : 1 < s.re) :
    (place2 ringOfIntegersEquivZsqrtdNeg5).asIdeal.absNorm = 2 ∧
    (place3 ringOfIntegersEquivZsqrtdNeg5).asIdeal.absNorm = 3 ∧
    (place3' ringOfIntegersEquivZsqrtdNeg5).asIdeal.absNorm = 3 ∧
    place2 ringOfIntegersEquivZsqrtdNeg5 ≠ place3 ringOfIntegersEquivZsqrtdNeg5 ∧
    place2 ringOfIntegersEquivZsqrtdNeg5 ≠ place3' ringOfIntegersEquivZsqrtdNeg5 ∧
    place3 ringOfIntegersEquivZsqrtdNeg5 ≠ place3' ringOfIntegersEquivZsqrtdNeg5 ∧
    (¬ ∃ α : 𝓞 QSqrtNeg5,
      (place2 ringOfIntegersEquivZsqrtdNeg5).asIdeal = Ideal.span {α}) ∧
    HasProd (fun v : HeightOneSpectrum (𝓞 QSqrtNeg5) ↦
      (1 - (v.asIdeal.absNorm : ℂ) ^ (-s))⁻¹) (dedekindZeta QSqrtNeg5 s) ∧
    (1 : HeckeCharacter (𝓞 QSqrtNeg5) QSqrtNeg5).LSeries s =
      dedekindZeta QSqrtNeg5 s := by
  have h1 := places_absNorm_distinct_identities_and_nonprincipal
    ringOfIntegersEquivZsqrtdNeg5
  have h2 := numberField_zsqrtdNeg5_dedekindZeta_and_hecke_bridge
    ringOfIntegersEquivZsqrtdNeg5 hs
  exact ⟨h1.1, h1.2.1, h1.2.2.1, h1.2.2.2.1, h1.2.2.2.2.1, h1.2.2.2.2.2.1,
    h1.2.2.2.2.2.2.2.2.2.2.1, h2.1, h2.2.1⟩

end InfoGeometry.Arithmetic.EvanstonLec8DedekindZetaQSqrtNeg5
