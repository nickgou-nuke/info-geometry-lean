/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Combinatorics.GolayConstructionA
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Sqrt

/-!
# The Leech lattice numerator construction

This file restores the genuine Golay congruence construction that was hidden
behind the former numerical `LeechLatticeNormData` witness.

We first construct the integral numerator set.  Its conventional real
realization is obtained by multiplying every coordinate by `1 / sqrt 8`.
Using the extended binary Golay code `C`, the two numerator branches are

* `2 c + 4 z`, with `sum z` even;
* `1 + 2 c + 4 z`, with `sum z` odd.

Here a binary codeword is lifted coordinatewise to `{0,1} ⊂ Z`. This is a
Golay-based numerator carrier with the displayed parity constraints. The file
proves it is an additive subgroup, proves common coordinate parity, establishes
the `1 / sqrt 8` norm-scaling identity, and exhibits vectors with scaled squared
norm four. It does not identify the scaled subgroup with the standard Leech
lattice or prove that the parity condition removes every shorter nonzero vector.

The minimum-norm, integrality, and unimodularity theorems are separate
obligations.  They are not represented by evidence fields in this owner.
-/

namespace InfoGeometry.Combinatorics.LeechLattice

open InfoGeometry.Combinatorics.ExtendedBinaryGolay
open InfoGeometry.Combinatorics.GolayConstructionA

/-- Canonical integral representative of a binary scalar. -/
def bitLift (b : F₂) : ℤ :=
  if b = 0 then 0 else 1

/-- Coordinatewise `{0,1}` lift of a binary word. -/
def wordLift (c : Word24) : IntegerWord24 :=
  fun i => bitLift (c i)

@[simp]
theorem wordLift_zero :
    wordLift 0 = 0 := by
  funext i
  simp [wordLift, bitLift]

@[simp]
theorem wordLift_one :
    wordLift 1 = 1 := by
  funext i
  simp [wordLift, bitLift]

/-- Sum of the integral coordinates of a length-24 word. -/
def coordinateSum (z : IntegerWord24) : ℤ :=
  ∑ i, z i

private theorem even_add_even_int {x y : ℤ} (hx : Even x) (hy : Even y) :
    Even (x + y) := by
  rcases hx with ⟨m, rfl⟩
  rcases hy with ⟨n, rfl⟩
  exact ⟨m + n, by ring⟩

private theorem odd_add_even_int {x y : ℤ} (hx : Odd x) (hy : Even y) :
    Odd (x + y) := by
  rcases hx with ⟨m, rfl⟩
  rcases hy with ⟨n, rfl⟩
  exact ⟨m + n, by ring⟩

private theorem odd_add_odd_int {x y : ℤ} (hx : Odd x) (hy : Odd y) :
    Even (x + y) := by
  rcases hx with ⟨m, rfl⟩
  rcases hy with ⟨n, rfl⟩
  exact ⟨m + n + 1, by ring⟩

/-- Even numerator branch `2 c + 4 z`. -/
def evenNumerator (c : Word24) (z : IntegerWord24) : IntegerWord24 :=
  fun i => 2 * wordLift c i + 4 * z i

/-- Odd numerator branch `1 + 2 c + 4 z`. -/
def oddNumerator (c : Word24) (z : IntegerWord24) : IntegerWord24 :=
  fun i => 1 + 2 * wordLift c i + 4 * z i

/-- Native even branch of the Golay neighbor construction. -/
def evenBranch : Set IntegerWord24 :=
  {a | ∃ c ∈ codeSubmodule, ∃ z, Even (coordinateSum z) ∧
      a = evenNumerator c z}

/-- Native odd branch of the Golay neighbor construction. -/
def oddBranch : Set IntegerWord24 :=
  {a | ∃ c ∈ codeSubmodule, ∃ z, Odd (coordinateSum z) ∧
      a = oddNumerator c z}

/--
Integral numerator carrier of the Leech lattice.  The geometric lattice is
its image under coordinatewise multiplication by `1 / sqrt 8`.
-/
def numerator : Set IntegerWord24 :=
  evenBranch ∪ oddBranch

/-- The Leech numerator carrier contains the origin. -/
theorem zero_mem_numerator :
    (0 : IntegerWord24) ∈ numerator := by
  have hz : Even (coordinateSum (0 : IntegerWord24)) := by
    simp [coordinateSum]
  have hzero : evenNumerator (0 : Word24) (0 : IntegerWord24) = 0 := by
    funext i
    simp [evenNumerator, wordLift, bitLift]
  rw [← hzero]
  exact Or.inl ⟨0, codeSubmodule.zero_mem, 0, hz, rfl⟩

/-- The integral lift of a binary word sums to its Hamming weight. -/
theorem coordinateSum_wordLift (c : Word24) :
    coordinateSum (wordLift c) = (hammingWeight c : ℤ) := by
  have hw : (hammingWeight c : ℤ) =
      ∑ i, (if c i = 0 then 0 else 1 : ℤ) := by
    simp only [hammingWeight, Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    by_cases h : c i = 0 <;> simp [h]
  rw [hw]
  unfold coordinateSum wordLift
  refine Finset.sum_congr rfl (fun i _ => ?_)
  unfold bitLift
  by_cases h : c i = 0 <;> simp [h]

/-- Complementing a binary word complements its `{0,1}` integral lift. -/
theorem wordLift_complement (c : Word24) :
    wordLift (1 + c) = fun i => 1 - wordLift c i := by
  funext i
  change bitLift (1 + c i) = 1 - bitLift (c i)
  have hv : (c i).val < 2 := ZMod.val_lt _
  by_cases h : (c i).val = 0
  · have hc0 : c i = 0 := by
      apply ZMod.val_injective 2
      rw [h, ZMod.val_zero]
    rw [hc0]
    norm_num [bitLift]
  · have hval : (c i).val = 1 := by omega
    have hc1 : c i = 1 := by
      apply ZMod.val_injective 2
      rw [hval, ZMod.val_one]
    have hadd : (1 : F₂) + 1 = 0 := by
      change (2 : ZMod 2) = 0
      exact ZMod.natCast_self 2
    rw [hc1, hadd]
    norm_num [bitLift]

/-- Integer carry created when adding two binary coordinate lifts. -/
def wordCarry (c d : Word24) : IntegerWord24 :=
  fun i => if c i = 1 ∧ d i = 1 then 1 else 0

/-- The lift of binary addition differs from integral addition by twice the carry. -/
theorem wordLift_add_carry (c d : Word24) :
    wordLift c + wordLift d = wordLift (c + d) + 2 • wordCarry c d := by
  funext i
  have hchar : (1 : F₂) + 1 = 0 := by
    change (2 : ZMod 2) = 0
    exact ZMod.natCast_self 2
  have bit_cases (x : F₂) : x = 0 ∨ x = 1 := by
    have hx : x.val < 2 := x.isLt
    by_cases h : x.val = 0
    · exact Or.inl ((ZMod.val_eq_zero x).mp h)
    · have hone : x.val = 1 := by omega
      exact Or.inr ((ZMod.val_eq_one (by decide) x).mp hone)
  rcases bit_cases (c i) with hc | hc <;>
    rcases bit_cases (d i) with hd | hd <;>
    simp [wordLift, bitLift, wordCarry, hc, hd, hchar]

/-- The carry count is even for two extended Golay codewords. -/
theorem wordCarry_sum_even {c d : Word24}
    (hc : c ∈ codeSubmodule) (hd : d ∈ codeSubmodule) :
    Even (coordinateSum (wordCarry c d)) := by
  have hchar : (1 : F₂) + 1 = 0 := by
    change (2 : ZMod 2) = 0
    exact ZMod.natCast_self 2
  have hwt (w : Word24) :
      (hammingWeight w : ℤ) = ∑ i, (if w i = 0 then 0 else 1 : ℤ) := by
    simp only [hammingWeight, Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    by_cases h : w i = 0 <;> simp [h]
  have hcount :
      (hammingWeight c : ℤ) + (hammingWeight d : ℤ) =
        (hammingWeight (c + d) : ℤ) + 2 * coordinateSum (wordCarry c d) := by
    rw [hwt c, hwt d, hwt (c + d)]
    have hpoint (i : Fin 24) :
        (if c i = 0 then 0 else 1 : ℤ) + (if d i = 0 then 0 else 1 : ℤ) =
          (if c i + d i = 0 then 0 else 1 : ℤ) +
            2 * (if c i = 1 ∧ d i = 1 then 1 else 0 : ℤ) := by
      have bit_cases (x : F₂) : x = 0 ∨ x = 1 := by
        have hx : x.val < 2 := x.isLt
        by_cases h : x.val = 0
        · exact Or.inl ((ZMod.val_eq_zero x).mp h)
        · exact Or.inr ((ZMod.val_eq_one (by decide) x).mp (by omega))
      rcases bit_cases (c i) with hc' | hc' <;>
        rcases bit_cases (d i) with hd' | hd' <;>
        simp [hc', hd', hchar]
    change (∑ i, (if c i = 0 then 0 else 1 : ℤ)) +
        ∑ i, (if d i = 0 then 0 else 1 : ℤ) =
      (∑ i, (if c i + d i = 0 then 0 else 1 : ℤ)) +
        2 * ∑ i, (if c i = 1 ∧ d i = 1 then 1 else 0 : ℤ)
    calc
      (∑ i, (if c i = 0 then 0 else 1 : ℤ)) +
          ∑ i, (if d i = 0 then 0 else 1 : ℤ) =
        ∑ i, ((if c i = 0 then 0 else 1 : ℤ) + (if d i = 0 then 0 else 1 : ℤ)) := by
          rw [Finset.sum_add_distrib]
      _ = ∑ i, ((if c i + d i = 0 then 0 else 1 : ℤ) +
          2 * (if c i = 1 ∧ d i = 1 then 1 else 0 : ℤ)) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hpoint i
      _ = (∑ i, (if c i + d i = 0 then 0 else 1 : ℤ)) +
          2 * ∑ i, (if c i = 1 ∧ d i = 1 then 1 else 0 : ℤ) := by
          simp only [Finset.sum_add_distrib, Finset.mul_sum]
  have hdiv_c := four_dvd_hammingWeight c
    ((mem_code_iff_mem_codeSubmodule c).mpr hc)
  have hdiv_d := four_dvd_hammingWeight d
    ((mem_code_iff_mem_codeSubmodule d).mpr hd)
  have hdiv_sum := four_dvd_hammingWeight (c + d)
    ((mem_code_iff_mem_codeSubmodule (c + d)).mpr (codeSubmodule.add_mem hc hd))
  have hcarry_even : Even (coordinateSum (wordCarry c d)) := by
    obtain ⟨a, ha⟩ : (4 : ℤ) ∣ (hammingWeight c : ℤ) := by exact_mod_cast hdiv_c
    obtain ⟨b, hb⟩ : (4 : ℤ) ∣ (hammingWeight d : ℤ) := by exact_mod_cast hdiv_d
    obtain ⟨e, he⟩ : (4 : ℤ) ∣ (hammingWeight (c + d) : ℤ) := by exact_mod_cast hdiv_sum
    refine ⟨a + b - e, ?_⟩
    have hlinear : 4 * a + 4 * b = 4 * e + 2 * coordinateSum (wordCarry c d) := by
      calc
        4 * a + 4 * b = (hammingWeight c : ℤ) + (hammingWeight d : ℤ) := by rw [ha, hb]
        _ = (hammingWeight (c + d) : ℤ) + 2 * coordinateSum (wordCarry c d) := hcount
        _ = 4 * e + 2 * coordinateSum (wordCarry c d) := by rw [he]
    omega
  exact hcarry_even

/-- The integral numerator set is closed under addition. -/
theorem add_mem_numerator {a b : IntegerWord24}
    (ha : a ∈ numerator) (hb : b ∈ numerator) : a + b ∈ numerator := by
  rcases ha with ⟨c, hc, z, hz, rfl⟩ | ⟨c, hc, z, hz, rfl⟩ <;>
    rcases hb with ⟨d, hd, w, hw, rfl⟩ | ⟨d, hd, w, hw, rfl⟩
  · let z' : IntegerWord24 := z + w + wordCarry c d
    obtain ⟨m, hm⟩ := hz
    obtain ⟨n, hn⟩ := hw
    obtain ⟨k, hk⟩ := wordCarry_sum_even hc hd
    have hz' : Even (coordinateSum z') := by
      refine ⟨m + n + k, ?_⟩
      rw [show coordinateSum z' = coordinateSum z + coordinateSum w +
          coordinateSum (wordCarry c d) by
        simp [z', coordinateSum, Finset.sum_add_distrib], hm, hn, hk]
      ring
    have hvec : evenNumerator c z + evenNumerator d w = evenNumerator (c + d) z' := by
      funext i
      change 2 * wordLift c i + 4 * z i + (2 * wordLift d i + 4 * w i) =
        2 * wordLift (c + d) i + 4 * (z i + w i + wordCarry c d i)
      have hbit := congrFun (wordLift_add_carry c d) i
      dsimp at hbit
      linear_combination 2 * hbit
    rw [hvec]
    exact Or.inl ⟨c + d, codeSubmodule.add_mem hc hd, z', hz', rfl⟩
  · let z' : IntegerWord24 := z + w + wordCarry c d
    obtain ⟨m, hm⟩ := hz
    obtain ⟨n, hn⟩ := hw
    obtain ⟨k, hk⟩ := wordCarry_sum_even hc hd
    have hz' : Odd (coordinateSum z') := by
      refine ⟨m + n + k, ?_⟩
      rw [show coordinateSum z' = coordinateSum z + coordinateSum w +
          coordinateSum (wordCarry c d) by
        simp [z', coordinateSum, Finset.sum_add_distrib], hm, hn, hk]
      ring
    have hvec : evenNumerator c z + oddNumerator d w =
        oddNumerator (c + d) z' := by
      funext i
      change 2 * wordLift c i + 4 * z i +
          (1 + 2 * wordLift d i + 4 * w i) =
        1 + 2 * wordLift (c + d) i + 4 * (z i + w i + wordCarry c d i)
      have hbit := congrFun (wordLift_add_carry c d) i
      dsimp at hbit
      linear_combination 2 * hbit
    rw [hvec]
    exact Or.inr ⟨c + d, codeSubmodule.add_mem hc hd, z', hz', rfl⟩
  · let z' : IntegerWord24 := z + w + wordCarry c d
    obtain ⟨m, hm⟩ := hz
    obtain ⟨n, hn⟩ := hw
    obtain ⟨k, hk⟩ := wordCarry_sum_even hc hd
    have hz' : Odd (coordinateSum z') := by
      refine ⟨m + n + k, ?_⟩
      rw [show coordinateSum z' = coordinateSum z + coordinateSum w +
          coordinateSum (wordCarry c d) by
        simp [z', coordinateSum, Finset.sum_add_distrib], hm, hn, hk]
      ring
    have hvec : oddNumerator c z + evenNumerator d w =
        oddNumerator (c + d) z' := by
      funext i
      change 1 + 2 * wordLift c i + 4 * z i +
          (2 * wordLift d i + 4 * w i) =
        1 + 2 * wordLift (c + d) i + 4 * (z i + w i + wordCarry c d i)
      have hbit := congrFun (wordLift_add_carry c d) i
      dsimp at hbit
      linear_combination 2 * hbit
    rw [hvec]
    exact Or.inr ⟨c + d, codeSubmodule.add_mem hc hd, z', hz', rfl⟩
  · let s : Word24 := c + d
    let c' : Word24 := 1 + s
    let z' : IntegerWord24 := z + w + wordCarry c d + wordLift s
    have hc' : c' ∈ codeSubmodule :=
      codeSubmodule.add_mem one_mem_codeSubmodule (codeSubmodule.add_mem hc hd)
    have hsum_s : Even (coordinateSum (wordLift s)) := by
      obtain ⟨k, hk⟩ : (4 : ℤ) ∣ (hammingWeight s : ℤ) := by
        exact_mod_cast four_dvd_hammingWeight s
          ((mem_code_iff_mem_codeSubmodule s).mpr (codeSubmodule.add_mem hc hd))
      rw [coordinateSum_wordLift, hk]
      exact ⟨2 * k, by ring⟩
    have hz' : Even (coordinateSum z') := by
      obtain ⟨m, hm⟩ := hz
      obtain ⟨n, hn⟩ := hw
      obtain ⟨k, hk⟩ := wordCarry_sum_even hc hd
      obtain ⟨e, he⟩ := hsum_s
      refine ⟨m + n + 1 + k + e, ?_⟩
      rw [show coordinateSum z' = coordinateSum z + coordinateSum w +
          coordinateSum (wordCarry c d) + coordinateSum (wordLift s) by
        simp [z', coordinateSum, Finset.sum_add_distrib, add_assoc], hm, hn, hk, he]
      ring
    have hvec : oddNumerator c z + oddNumerator d w = evenNumerator c' z' := by
      funext i
      change 1 + 2 * wordLift c i + 4 * z i +
          (1 + 2 * wordLift d i + 4 * w i) =
        2 * wordLift c' i +
          4 * (z i + w i + wordCarry c d i + wordLift s i)
      rw [show wordLift c' = fun j => 1 - wordLift s j by
        simp [c', s, wordLift_complement]]
      have hbit := congrFun (wordLift_add_carry c d) i
      dsimp at hbit
      linear_combination 2 * hbit
    rw [hvec]
    exact Or.inl ⟨c', hc', z', hz', rfl⟩

/-- Negation preserves the even/odd parity condition in the Golay numerator
branches, so the numerator carrier is closed under additive inverses. -/
theorem neg_mem_numerator {a : IntegerWord24} (ha : a ∈ numerator) :
    -a ∈ numerator := by
  rcases ha with ⟨c, hc, z, hz, rfl⟩ | ⟨c, hc, z, hz, rfl⟩
  · let z' : IntegerWord24 := fun i => -wordLift c i - z i
    have hweight := four_dvd_hammingWeight c
      ((mem_code_iff_mem_codeSubmodule c).mpr hc)
    obtain ⟨k, hk⟩ : (4 : ℤ) ∣ (hammingWeight c : ℤ) := by
      exact_mod_cast hweight
    obtain ⟨m, hm⟩ := hz
    have hsum : coordinateSum z' = - (hammingWeight c : ℤ) - coordinateSum z := by
      calc
        coordinateSum z' = -coordinateSum (wordLift c) - coordinateSum z := by
          simp [z', coordinateSum, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
        _ = - (hammingWeight c : ℤ) - coordinateSum z := by rw [coordinateSum_wordLift]
    have hz' : Even (coordinateSum z') := by
      refine ⟨-2 * k - m, ?_⟩
      rw [hsum, hk, hm]
      ring_nf
    have hneg : -evenNumerator c z = evenNumerator c z' := by
      funext i
      change -(2 * wordLift c i + 4 * z i) =
        2 * wordLift c i + 4 * (-wordLift c i - z i)
      ring
    rw [hneg]
    exact Or.inl ⟨c, hc, z', hz', rfl⟩
  · let c' : Word24 := 1 + c
    let z' : IntegerWord24 := fun i => -1 - z i
    have hc' : c' ∈ codeSubmodule :=
      codeSubmodule.add_mem one_mem_codeSubmodule hc
    have hcomp : wordLift c' = fun i => 1 - wordLift c i := by
      funext i
      change bitLift (1 + c i) = 1 - bitLift (c i)
      have hv : (c i).val < 2 := ZMod.val_lt _
      by_cases h : (c i).val = 0
      · have hc0 : c i = 0 := by
          apply ZMod.val_injective 2
          rw [h, ZMod.val_zero]
        rw [hc0]
        norm_num [bitLift]
      · have hval : (c i).val = 1 := by omega
        have hc1 : c i = 1 := by
          apply ZMod.val_injective 2
          rw [hval, ZMod.val_one]
        have hadd : (1 : F₂) + 1 = 0 := by
          change (2 : ZMod 2) = 0
          exact ZMod.natCast_self 2
        rw [hc1, hadd]
        norm_num [bitLift]
    obtain ⟨m, hm⟩ := hz
    have hsum : coordinateSum z' = -24 - coordinateSum z := by
      simp [z', coordinateSum, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
    have hz' : Odd (coordinateSum z') := by
      refine ⟨-13 - m, ?_⟩
      rw [hsum, hm]
      ring
    have hneg : -oddNumerator c z = oddNumerator c' z' := by
      funext i
      change -(1 + 2 * wordLift c i + 4 * z i) =
        1 + 2 * wordLift c' i + 4 * (-1 - z i)
      rw [hcomp]
      ring
    rw [hneg]
    exact Or.inr ⟨c', hc', z', hz', rfl⟩

/-- The Golay numerator is an additive subgroup of the integral coordinate
module. This packages the proved zero, addition, and negation closure without
claiming yet that its scaled real image is the standard Leech lattice. -/
def numeratorAddSubgroup : AddSubgroup IntegerWord24 where
  carrier := numerator
  zero_mem' := zero_mem_numerator
  add_mem' := fun ha hb => add_mem_numerator ha hb
  neg_mem' := fun ha => neg_mem_numerator ha

/-- Every even-branch numerator has even coordinates. -/
theorem evenNumerator_coordinate_even
    (c : Word24) (z : IntegerWord24) (i : Fin 24) :
    Even (evenNumerator c z i) := by
  refine ⟨wordLift c i + 2 * z i, ?_⟩
  simp [evenNumerator]
  ring

/-- Every odd-branch numerator has odd coordinates. -/
theorem oddNumerator_coordinate_odd
    (c : Word24) (z : IntegerWord24) (i : Fin 24) :
    Odd (oddNumerator c z i) := by
  refine ⟨wordLift c i + 2 * z i, ?_⟩
  simp [oddNumerator]
  ring

/--
The common-parity condition is derived from membership in the Leech
numerator carrier; it is not stored as a Boolean marker.
-/
theorem hasCommonParity_of_mem
    {a : IntegerWord24} (ha : a ∈ numerator) :
    (∀ i, Even (a i)) ∨ (∀ i, Odd (a i)) := by
  rcases ha with ha | ha
  · rcases ha with ⟨c, hc, z, hz, rfl⟩
    exact Or.inl (evenNumerator_coordinate_even c z)
  · rcases ha with ⟨c, hc, z, hz, rfl⟩
    exact Or.inr (oddNumerator_coordinate_odd c z)

/-- Conventional coordinatewise real scaling by `1 / sqrt 8`. -/
noncomputable def scaledRealization
    (a : IntegerWord24) : Fin 24 → ℝ :=
  fun i => (a i : ℝ) / Real.sqrt 8

/-- Integral squared-norm numerator used before the `1 / sqrt 8` scaling. -/
def normSqNumerator (a : IntegerWord24) : ℤ :=
  ∑ i, a i * a i

/--
Squared Euclidean norm of the scaled realization, expressed by the integral
numerator.  This is the normalization bridge needed by the future rootlessness
and minimum-norm proof.
-/
theorem scaledRealization_normSq (a : IntegerWord24) :
    ∑ i, scaledRealization a i * scaledRealization a i =
      (normSqNumerator a : ℝ) / 8 := by
  simp only [scaledRealization, normSqNumerator, Int.cast_sum, Int.cast_mul]
  calc
    (∑ i, (a i : ℝ) / Real.sqrt 8 * ((a i : ℝ) / Real.sqrt 8)) =
        ∑ i, ((a i : ℝ) * (a i : ℝ)) / 8 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [div_mul_div_comm]
      rw [Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 8)]
    _ = (∑ i, (a i : ℝ) * (a i : ℝ)) / 8 := by
      simp only [div_eq_mul_inv]
      rw [Finset.sum_mul]

/-- A concrete integral parameter with two unit coordinates and even total. -/
def twoCoordinateParameter : IntegerWord24 :=
  fun i => if i.val < 2 then 1 else 0

/-- The Leech numerator carrier contains an actual nonzero vector of norm four
after the conventional `1 / sqrt 8` scaling. This witnesses the scale of the
constructed carrier; it does not assert that four is the minimum norm. -/
theorem exists_scaled_norm_four_vector :
    ∃ a ∈ numerator, a ≠ 0 ∧
      (∑ i, scaledRealization a i * scaledRealization a i) = 4 := by
  let z := twoCoordinateParameter
  let a := evenNumerator (0 : Word24) z
  have hz : Even (coordinateSum z) := by
    refine ⟨1, ?_⟩
    decide
  have ha : a ∈ numerator := by
    exact Or.inl ⟨0, codeSubmodule.zero_mem, z, hz, rfl⟩
  have hnorm : normSqNumerator a = 32 := by
    norm_num [a, evenNumerator, wordLift, bitLift, z,
      twoCoordinateParameter, normSqNumerator]
    <;> decide
  have hne : a ≠ 0 := by
    intro hzero
    rw [hzero] at hnorm
    norm_num [normSqNumerator] at hnorm
  refine ⟨a, ha, hne, ?_⟩
  rw [scaledRealization_normSq, hnorm]
  norm_num

/-- Integer word with prescribed values in two distinct coordinates. -/
def twoCoordinateParameterAt (i j : Fin 24) (r s : ℤ) : IntegerWord24 :=
  fun k => (if k = i then r else 0) + (if k = j then s else 0)

/-- Every choice of two distinct coordinates and signs gives a genuine member
of the constructed Leech numerator whose conventional scaled squared norm is
four. This proves existence for the whole signed two-coordinate family; it
does not assert the full kissing-number count or identify the numerator
carrier with the standard Leech lattice. -/
theorem signed_two_coordinate_vector_has_scaled_norm_four
    (i j : Fin 24) (hij : i ≠ j) (r s : ℤ)
    (hr : r = 1 ∨ r = -1) (hs : s = 1 ∨ s = -1) :
    let z := twoCoordinateParameterAt i j r s
    let a := evenNumerator (0 : Word24) z
    a ∈ numerator ∧ a ≠ 0 ∧
      (∑ k, scaledRealization a k * scaledRealization a k) = 4 := by
  classical
  dsimp
  let z := twoCoordinateParameterAt i j r s
  let a := evenNumerator (0 : Word24) z
  have hsum_i : ∑ k : Fin 24, (if k = i then r else 0) = r := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro k hk hki
      simp [hki]
    · simp
  have hsum_j : ∑ k : Fin 24, (if k = j then s else 0) = s := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro k hk hkj
      simp [hkj]
    · simp
  have hsum : coordinateSum z = r + s := by
    simp only [coordinateSum, z, twoCoordinateParameterAt, Finset.sum_add_distrib]
    rw [hsum_i, hsum_j]
  have hz : Even (coordinateSum z) := by
    rw [hsum]
    rcases hr with rfl | rfl <;> rcases hs with rfl | rfl <;>
      norm_num [Even]
  have ha : a ∈ numerator := by
    exact Or.inl ⟨0, codeSubmodule.zero_mem, z, hz, rfl⟩
  have hnormz : normSqNumerator z = 2 := by
    have hpoint (k : Fin 24) :
        z k * z k = (if k = i then r * r else 0) + (if k = j then s * s else 0) := by
      by_cases hki : k = i
      · subst k
        simp [z, twoCoordinateParameterAt, hij]
      · by_cases hkj : k = j
        · subst k
          simp [z, twoCoordinateParameterAt, Ne.symm hij]
        · simp [z, twoCoordinateParameterAt, hki, hkj]
    calc
      normSqNumerator z = r * r + s * s := by
        calc
          normSqNumerator z = ∑ k, ((if k = i then r * r else 0) +
              (if k = j then s * s else 0)) := by
            unfold normSqNumerator
            apply Finset.sum_congr rfl
            intro k hk
            exact hpoint k
          _ = (∑ k : Fin 24, (if k = i then r * r else 0)) +
              ∑ k : Fin 24, (if k = j then s * s else 0) := by
            rw [Finset.sum_add_distrib]
          _ = r * r + s * s := by
            have hsum_i_sq : ∑ k : Fin 24, (if k = i then r * r else 0) = r * r := by
              rw [Finset.sum_eq_single i]
              · simp
              · intro k hk hki
                simp [hki]
              · simp
            have hsum_j_sq : ∑ k : Fin 24, (if k = j then s * s else 0) = s * s := by
              rw [Finset.sum_eq_single j]
              · simp
              · intro k hk hkj
                simp [hkj]
              · simp
            rw [hsum_i_sq, hsum_j_sq]
      _ = 2 := by
        rcases hr with rfl | rfl <;> rcases hs with rfl | rfl <;> norm_num
  have hnorm : normSqNumerator a = 32 := by
    calc
      normSqNumerator a = ∑ k, 16 * (z k * z k) := by
        apply Finset.sum_congr rfl
        intro k hk
        simp [a, evenNumerator, wordLift_zero]
        ring
      _ = 16 * normSqNumerator z := by
        simp [normSqNumerator, Finset.mul_sum]
      _ = 32 := by rw [hnormz]; norm_num
  have hne : a ≠ 0 := by
    intro hzero
    rw [hzero] at hnorm
    norm_num [normSqNumerator] at hnorm
  refine ⟨ha, hne, ?_⟩
  rw [scaledRealization_normSq, hnorm]
  norm_num

theorem bitLift_zero :
    bitLift 0 = 0 := by
  simp [bitLift]

@[simp]

theorem bitLift_one :
    bitLift 1 = 1 := by
  simp [bitLift]

theorem coordinateSum_zero :
    coordinateSum 0 = 0 := by
  simp [coordinateSum]


theorem evenNumerator_mem
    {c : Word24} (hc : c ∈ codeSubmodule)
    {z : IntegerWord24} (hz : Even (coordinateSum z)) :
    evenNumerator c z ∈ numerator := by
  left
  exact ⟨c, hc, z, hz, rfl⟩


theorem oddNumerator_mem
    {c : Word24} (hc : c ∈ codeSubmodule)
    {z : IntegerWord24} (hz : Odd (coordinateSum z)) :
    oddNumerator c z ∈ numerator := by
  right
  exact ⟨c, hc, z, hz, rfl⟩

/-- All coordinates of an integral word have the same parity. -/
def HasCommonParity (a : IntegerWord24) : Prop :=
  (∀ i, Even (a i)) ∨ (∀ i, Odd (a i))

theorem normSqNumerator_zero :
    normSqNumerator 0 = 0 := by
  simp [normSqNumerator]

end InfoGeometry.Combinatorics.LeechLattice
