/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Combinatorics.LeechLattice

/-!
# Evenness and integrality of the Golay Construction-A lattice and the Leech numerator

Discharges the integrality/evenness obligations left open in
`InfoGeometry.Combinatorics.GolayConstructionA` and `InfoGeometry.Combinatorics.LeechLattice`,
from the Golay facts already proved there (`four_dvd_hammingWeight`, `self_orthogonal`).

* Construction A (`x mod 2 ∈ C`): `Σ xᵢ² ≡ wt(x mod 2) (mod 4)` and
  `Σ xᵢ yᵢ ≡ dot (x mod 2) (y mod 2) (mod 2)`; hence for the Golay lattice
  `4 ∣ Σ xᵢ²` and `2 ∣ Σ xᵢ yᵢ` (the `1/√2`-scaled lattice is even integral).
* Leech numerator (`2c + 4z`, `Σz` even; `1 + 2c + 4z`, `Σz` odd): `16 ∣ Σ aᵢ²` and
  `8 ∣ Σ aᵢ bᵢ`; hence the `1/√8`-scaled Leech lattice is even integral.

Not proved here: unimodularity, rootlessness (minimum norm `4`), the kissing number.

## BUCKET 1: Kernel-verified finite arithmetic
The norm and inner-product congruences, divisibility statements, and scaled
metric conclusions below are proved for the explicitly defined carriers.

## BUCKET 2: Conditional code-to-lattice consequences
The concrete encoded extended Golay code has an unconditional minimum-weight
theorem in `ExtendedBinaryGolay`. The even-branch estimate below consumes its
codeword-nonzero hypothesis; full numerator rootlessness still requires the
zero-codeword even branch and the odd numerator branch.

## BUCKET 3: Open lattice identification obligations
This module does not prove that the numerator is a lattice, unimodularity,
rootlessness, or a kissing-number classification.
-/

namespace InfoGeometry.Combinatorics.LeechEvenIntegral

open InfoGeometry.Combinatorics.ExtendedBinaryGolay
open InfoGeometry.Combinatorics.GolayConstructionA
open InfoGeometry.Combinatorics.LeechLattice

/-! ### Elementary parity facts -/

/-- `x² ≡ (x mod 2) (mod 4)` as an exact divisibility. -/
theorem four_dvd_sq_sub_bit (x : ℤ) :
    4 ∣ x * x - (if (x : ZMod 2) = 0 then 0 else 1) := by
  rcases Int.even_or_odd' x with ⟨k, rfl | rfl⟩
  · have : ((2 * k : ℤ) : ZMod 2) = 0 := by push_cast; simp [show (2 : ZMod 2) = 0 from rfl]
    rw [if_pos this]; exact ⟨k * k, by ring⟩
  · have : ((2 * k + 1 : ℤ) : ZMod 2) ≠ 0 := by
      push_cast; simp [show (2 : ZMod 2) = 0 from rfl]
    rw [if_neg this]; exact ⟨k * k + k, by ring⟩

/-- Hamming weight as a sum of indicator values. -/
theorem hammingWeight_eq_sum {n : ℕ} (w : Fin n → F₂) :
    (hammingWeight w : ℤ) = ∑ i, (if w i = 0 then 0 else 1 : ℤ) := by
  simp only [hammingWeight, Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases h : w i = 0 <;> simp [h]

/-- Construction A norm law: `Σ xᵢ² ≡ wt(x mod 2) (mod 4)`. -/
theorem four_dvd_normSq_sub_weight {n : ℕ} (x : Fin n → ℤ) :
    4 ∣ (∑ i, x i * x i) - (hammingWeight (fun i => (x i : F₂)) : ℤ) := by
  rw [hammingWeight_eq_sum, ← Finset.sum_sub_distrib]
  exact Finset.dvd_sum (fun i _ => four_dvd_sq_sub_bit (x i))

/-- Construction A inner-product law: `Σ xᵢ yᵢ ≡ dot (x mod 2) (y mod 2) (mod 2)`. -/
theorem cast_inner {n : ℕ} (x y : Fin n → ℤ) :
    ((∑ i, x i * y i : ℤ) : F₂) = dot (fun i => (x i : F₂)) (fun i => (y i : F₂)) := by
  simp [dot]

/-! ### The Golay Construction-A lattice is even integral after `1/√2` scaling -/

/-- A Construction-A Golay vector has squared-norm numerator divisible by four. -/
theorem golayA_four_dvd_normSq {x : IntegerWord24} (hx : x ∈ lattice) :
    4 ∣ GolayConstructionA.normSqNumerator x := by
  have hw := four_dvd_hammingWeight _
    ((mem_lattice_iff_reduction_mem_code x).mp hx)
  have h := four_dvd_normSq_sub_weight x
  have hw' : (4 : ℤ) ∣ (hammingWeight (fun i => (x i : F₂)) : ℤ) := by
    exact_mod_cast hw
  have := dvd_add h hw'
  simpa [GolayConstructionA.normSqNumerator] using this

/-- Two Construction-A Golay vectors have an even integral inner-product numerator. -/
theorem golayA_two_dvd_inner {x y : IntegerWord24} (hx : x ∈ lattice) (hy : y ∈ lattice) :
    2 ∣ ∑ i, x i * y i := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp
  rw [cast_inner]
  exact self_orthogonal _ ((mem_lattice_iff_reduction_mem_code x).mp hx) _
    ((mem_lattice_iff_reduction_mem_code y).mp hy)

/-! ### The Leech numerator lattice is even integral after `1/√8` scaling -/

/-- The chosen `{0,1}` integer lift preserves the idempotent bit square. -/
theorem bitLift_sq (b : F₂) : bitLift b * bitLift b = bitLift b := by
  fin_cases b <;> simp [bitLift]

/-- Reducing the canonical integer lift modulo two recovers the original bit. -/
theorem bitLift_cast (b : F₂) : ((bitLift b : ℤ) : F₂) = b := by
  fin_cases b
  · change ((bitLift (0 : F₂) : ℤ) : F₂) = 0
    simp [bitLift]
  · change ((bitLift (1 : F₂) : ℤ) : F₂) = 1
    simp [bitLift]

/-- The coordinate sum of a lifted Golay word equals its Hamming weight. -/
theorem sum_wordLift (c : Word24) : ∑ i, wordLift c i = (hammingWeight c : ℤ) := by
  rw [hammingWeight_eq_sum]
  rfl

/-- Integer lifts of two Golay words have even inner-product numerator. -/
theorem two_dvd_lift_inner {c c' : Word24} (hc : c ∈ codeSubmodule) (hc' : c' ∈ codeSubmodule) :
    2 ∣ ∑ i, wordLift c i * wordLift c' i := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp
  rw [cast_inner]
  have e1 : (fun i => ((wordLift c i : ℤ) : F₂)) = c := funext fun i => bitLift_cast (c i)
  have e2 : (fun i => ((wordLift c' i : ℤ) : F₂)) = c' := funext fun i => bitLift_cast (c' i)
  rw [e1, e2]
  exact self_orthogonal _ ((mem_code_iff_mem_codeSubmodule c).mpr hc) _
    ((mem_code_iff_mem_codeSubmodule c').mpr hc')

/-- Per-vector norm expansion of the even branch. -/
theorem normSq_even (c : Word24) (z : IntegerWord24) :
    LeechLattice.normSqNumerator (evenNumerator c z) =
      4 * hammingWeight c + 16 * ∑ i, (wordLift c i * z i + z i * z i) := by
  rw [← sum_wordLift, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have h := bitLift_sq (c i)
  simp only [evenNumerator, wordLift] at *
  linear_combination 4 * h

/-- Per-vector norm expansion of the odd branch. -/
theorem normSq_odd (c : Word24) (z : IntegerWord24) :
    LeechLattice.normSqNumerator (oddNumerator c z) =
      24 + 8 * hammingWeight c + 8 * coordinateSum z +
        16 * ∑ i, (wordLift c i * z i + z i * z i) := by
  rw [← sum_wordLift, coordinateSum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    show (24 : ℤ) = ∑ _i : Fin 24, (1 : ℤ) by simp, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have h := bitLift_sq (c i)
  simp only [oddNumerator, wordLift] at *
  linear_combination 4 * h

/-- Each coordinate correction in the even numerator norm expansion is
nonnegative: for a binary coordinate `b`, the integer polynomial is either
`z^2` or `z(z+1)`. -/
theorem bitLift_quadratic_nonneg (b : F₂) (z : ℤ) :
    0 ≤ bitLift b * z + z * z := by
  by_cases hb : b = 0
  · simp [bitLift, hb]
    exact mul_self_nonneg z
  · simp [bitLift, hb]
    by_cases hz : z < 0
    · have hz' : z + 1 ≤ 0 := by omega
      have hprod : 0 ≤ z * (z + 1) := mul_nonneg_of_nonpos_of_nonpos
        (le_of_lt hz) hz'
      nlinarith [hprod]
    · have hz' : 0 ≤ z := le_of_not_gt hz
      have hprod : 0 ≤ z * (z + 1) := mul_nonneg hz' (by omega)
      nlinarith [hprod]

/-- A nonzero Golay word contributes at least `32` to the even numerator
squared norm. This uses the unconditional minimum-weight theorem for the
concrete encoded Golay code, together with nonnegativity of every integer
coordinate correction. -/
theorem evenNumerator_normSq_ge_32_of_codeword_ne_zero
    {c : Word24} (hc : c ∈ codeSubmodule) (hc0 : c ≠ 0)
    (z : IntegerWord24) :
    32 ≤ LeechLattice.normSqNumerator (evenNumerator c z) := by
  have hweight := minimumWeight_eq_eight_finite.1 c
    ((mem_code_iff_mem_codeSubmodule c).2 hc) hc0
  have hterms : 0 ≤ ∑ i, (wordLift c i * z i + z i * z i) := by
    apply Finset.sum_nonneg
    intro i hi
    exact bitLift_quadratic_nonneg (c i) (z i)
  rw [normSq_even]
  have hweightZ : (8 : ℤ) ≤ (hammingWeight c : ℤ) := by exact_mod_cast hweight
  nlinarith

/-- **Evenness:** every Leech numerator vector has `16 ∣ Σ aᵢ²`, i.e. scaled norm `Σ aᵢ²/8` even. -/
theorem leech_sixteen_dvd_normSq {a : IntegerWord24} (ha : a ∈ numerator) :
    16 ∣ LeechLattice.normSqNumerator a := by
  rcases ha with ⟨c, hc, z, hz, rfl⟩ | ⟨c, hc, z, hz, rfl⟩
  · rw [normSq_even]
    have hweight := four_dvd_hammingWeight c ((mem_code_iff_mem_codeSubmodule c).mpr hc)
    have hweightInt : (4 : ℤ) ∣ (hammingWeight c : ℤ) := by exact_mod_cast hweight
    obtain ⟨k, hk⟩ := hweightInt
    rw [hk]
    exact ⟨k + ∑ i, (wordLift c i * z i + z i * z i), by ring⟩
  · rw [normSq_odd]
    have hweight := four_dvd_hammingWeight c ((mem_code_iff_mem_codeSubmodule c).mpr hc)
    have hweightInt : (4 : ℤ) ∣ (hammingWeight c : ℤ) := by exact_mod_cast hweight
    obtain ⟨k, hk⟩ := hweightInt
    obtain ⟨m, hm⟩ := hz
    rw [hk, hm]
    exact ⟨2 + 2 * k + m + ∑ i, (wordLift c i * z i + z i * z i), by ring⟩

/-- Inner-product numerator. -/
def innerNumerator (a b : IntegerWord24) : ℤ := ∑ i, a i * b i

/-- Expand an inner-product numerator for two even-branch vectors. -/
theorem inner_even_even (c c' : Word24) (z z' : IntegerWord24) :
    innerNumerator (evenNumerator c z) (evenNumerator c' z') =
      4 * ∑ i, wordLift c i * wordLift c' i +
        8 * ∑ i, (wordLift c i * z' i + z i * wordLift c' i + 2 * (z i * z' i)) := by
  simp only [innerNumerator, evenNumerator, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_); ring

/-- Expand an inner-product numerator for one even- and one odd-branch vector. -/
theorem inner_even_odd (c c' : Word24) (z z' : IntegerWord24) :
    innerNumerator (evenNumerator c z) (oddNumerator c' z') =
      2 * hammingWeight c + 4 * ∑ i, wordLift c i * wordLift c' i + 4 * coordinateSum z +
        8 * ∑ i, (wordLift c i * z' i + z i * wordLift c' i + 2 * (z i * z' i)) := by
  rw [← sum_wordLift, coordinateSum]
  simp only [innerNumerator, evenNumerator, oddNumerator, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_); ring

/-- Expand an inner-product numerator for two odd-branch vectors. -/
theorem inner_odd_odd (c c' : Word24) (z z' : IntegerWord24) :
    innerNumerator (oddNumerator c z) (oddNumerator c' z') =
      24 + 2 * hammingWeight c + 2 * hammingWeight c' + 4 * ∑ i, wordLift c i * wordLift c' i +
        4 * coordinateSum z + 4 * coordinateSum z' +
        8 * ∑ i, (wordLift c i * z' i + z i * wordLift c' i + 2 * (z i * z' i)) := by
  rw [← sum_wordLift, ← sum_wordLift, coordinateSum, coordinateSum,
    show (24 : ℤ) = ∑ _i : Fin 24, (1 : ℤ) by simp]
  simp only [innerNumerator, oddNumerator, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_); ring

/-- The integral coordinate inner-product numerator is symmetric. -/
theorem innerNumerator_comm (a b : IntegerWord24) : innerNumerator a b = innerNumerator b a := by
  simp only [innerNumerator, mul_comm]

/-- **Integrality:** any two Leech numerator vectors have `8 ∣ Σ aᵢ bᵢ`. -/
theorem leech_eight_dvd_inner {a b : IntegerWord24} (ha : a ∈ numerator) (hb : b ∈ numerator) :
    8 ∣ innerNumerator a b := by
  have key : ∀ {c c' : Word24}, c ∈ codeSubmodule → c' ∈ codeSubmodule →
      ∃ k k' d : ℤ, (hammingWeight c : ℤ) = 4 * k ∧ (hammingWeight c' : ℤ) = 4 * k' ∧
        ∑ i, wordLift c i * wordLift c' i = 2 * d := by
    intro c c' hc hc'
    have hw := four_dvd_hammingWeight c ((mem_code_iff_mem_codeSubmodule c).mpr hc)
    have hw' := four_dvd_hammingWeight c' ((mem_code_iff_mem_codeSubmodule c').mpr hc')
    have hwInt : (4 : ℤ) ∣ (hammingWeight c : ℤ) := by exact_mod_cast hw
    have hw'Int : (4 : ℤ) ∣ (hammingWeight c' : ℤ) := by exact_mod_cast hw'
    obtain ⟨k, hk⟩ := hwInt
    obtain ⟨k', hk'⟩ := hw'Int
    obtain ⟨d, hd⟩ := two_dvd_lift_inner hc hc'
    exact ⟨k, k', d, hk, hk', hd⟩
  rcases ha with ⟨c, hc, z, hz, rfl⟩ | ⟨c, hc, z, hz, rfl⟩ <;>
    rcases hb with ⟨c', hc', z', hz', rfl⟩ | ⟨c', hc', z', hz', rfl⟩ <;>
    obtain ⟨k, k', d, hk, hk', hd⟩ := key hc hc'
  · rw [inner_even_even, hd]
    exact ⟨d + ∑ i, (wordLift c i * z' i + z i * wordLift c' i + 2 * (z i * z' i)), by ring⟩
  · rw [inner_even_odd, hk, hd]
    obtain ⟨m, hm⟩ := hz
    rw [coordinateSum] at hm ⊢
    rw [hm]
    exact ⟨k + d + m + ∑ i, (wordLift c i * z' i + z i * wordLift c' i + 2 * (z i * z' i)),
      by ring⟩
  · rw [innerNumerator_comm, inner_even_odd]
    obtain ⟨d', hd'⟩ := two_dvd_lift_inner hc' hc
    rw [hk', hd']
    obtain ⟨m, hm⟩ := hz'
    rw [coordinateSum] at hm ⊢
    rw [hm]
    exact ⟨k' + d' + m +
      ∑ i, (wordLift c' i * z i + z' i * wordLift c i + 2 * (z' i * z i)), by ring⟩
  · rw [inner_odd_odd, hk, hk', hd]
    obtain ⟨m, hm⟩ := hz
    obtain ⟨m', hm'⟩ := hz'
    rw [coordinateSum, coordinateSum] at *
    rw [hm, hm']
    exact ⟨4 + k + k' + d + m + m' +
      ∑ i, (wordLift c i * z' i + z i * wordLift c' i + 2 * (z i * z' i)), by ring⟩

/-! ### Metric consequences in the actual scaled realization -/

/-- Real inner product after the conventional coordinatewise `1 / sqrt 8`
scaling. -/
noncomputable def scaledInnerProduct (a b : IntegerWord24) : ℝ :=
  ∑ i, scaledRealization a i * scaledRealization b i

/-- The scaled real inner product is the integral numerator divided by eight. -/
theorem scaledInnerProduct_eq (a b : IntegerWord24) :
    scaledInnerProduct a b = (innerNumerator a b : ℝ) / 8 := by
  simp only [scaledInnerProduct, scaledRealization, innerNumerator,
    Int.cast_sum, Int.cast_mul]
  calc
    (∑ i, (a i : ℝ) / Real.sqrt 8 * ((b i : ℝ) / Real.sqrt 8)) =
        ∑ i, ((a i : ℝ) * (b i : ℝ)) / 8 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [div_mul_div_comm]
      rw [Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 8)]
    _ = (∑ i, (a i : ℝ) * (b i : ℝ)) / 8 := by
      simp only [div_eq_mul_inv]
      rw [Finset.sum_mul]

/-- Every vector in the scaled numerator has even squared norm. This is a
metric consequence of numerator divisibility; it does not assert positivity
or a minimum norm. -/
theorem scaled_normSq_is_even_integer {a : IntegerWord24} (ha : a ∈ numerator) :
    ∃ k : ℤ,
      (∑ i, scaledRealization a i * scaledRealization a i) = (2 * k : ℝ) := by
  obtain ⟨k, hk⟩ := leech_sixteen_dvd_normSq ha
  refine ⟨k, ?_⟩
  rw [LeechLattice.scaledRealization_normSq, hk]
  norm_num [div_eq_mul_inv]
  ring

/-- Every pair of numerator vectors has integral inner product after the
conventional scaling. -/
theorem scaled_innerProduct_is_integer {a b : IntegerWord24}
    (ha : a ∈ numerator) (hb : b ∈ numerator) :
    ∃ k : ℤ, scaledInnerProduct a b = (k : ℝ) := by
  obtain ⟨k, hk⟩ := leech_eight_dvd_inner ha hb
  refine ⟨k, ?_⟩
  rw [scaledInnerProduct_eq, hk]
  norm_num [div_eq_mul_inv]
  ring

end InfoGeometry.Combinatorics.LeechEvenIntegral
