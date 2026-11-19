/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Projective.GrassmannMechanicsBarycenterAndPotentials
import InfoGeometry.Erlangen.ErlangenProgramCurvatureBinaryAndMasterAtlas
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.CliffordAlgebra.EvenEquiv
import Mathlib.LinearAlgebra.CliffordAlgebra.Equivs
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.QuadraticForm.Prod
import Mathlib.Tactic

/-!
# Clifford's *Applications of Grassmann's Extensive Algebra* (1878) Part I (`pp. 350–355`)

This module formalizes Archetypes `CL₁`, `CL₂`, `CL₃`, and **Bridges V, VIb, VIIa, VIIb** from
W. K. Clifford's *Applications of Grassmann's Extensive Algebra* (*American Journal of
Mathematics*, Vol. 1, No. 4, 1878, pp. 350–355):

1. **`n`-Unit Geometric Algebra `Cl(0, n)` (`pp. 351, 354–355`)**: Negative-definite quadratic
   form `cliffordNegSqForm R n` (`Q(ι_r) = -1`, polar product anticommutation `ι_r ι_s = -ι_s ι_r`),
   canonical ordered blades `cBlade R n S`, and the constructive faithful representation
   `cliffordEndRep` / `bladeRepr` proving linear independence and noncommutativity of `cBlade`.
2. **`CL₃` (`pp. 354–355`)**: General `n`-unit blade square law `(-1)^(m(m+1)/2)` and overlap
   commutation law `(-1)^(m*p - k^2)` together with Clifford's three corollaries.
3. **Bridge V (`Grassmann 1862` ↔ `Clifford 1878`, `p. 350`)**: Equivariant linear isomorphism
   `CliffordAlgebra.equivExterior` relating polar Clifford multiplication `ι u * ι v` to
   Grassmann exterior product minus scalar inner contraction (`ι u ∧ ι v - u ⬝ᵥ v`).
4. **`CL₁` (`pp. 351–353`) & Bridge VIIa (`Klein 1872 Fn. 37`)**: Realization of quaternion
   versors `i, j, k` as binary products `ι₂ ι₃, ι₃ ι₁, ι₁ ι₂` operating identically on rotors
   `ι₀ ι_r` and vectors `ι_r`, Maxwell force-vs-flow grade distinctness (`ι_r ≠ ι_s ι_t`), and
   spinor conjugation `q v q̃ = quatRotMatrix(q) *ᵥ v` in `Cl(0, 3)`.
5. **`CL₂` (`pp. 353–354`) & Bridges VIb, VIIb**: Elliptic 4-unit volume element `ω₄ = ι₀ ι₁ ι₂ ι₃`
   (`ω₄² = 1`), polar hyperplane anticommutation `ω₄ ι_r = -ι_r ω₄` (**Bridge VIIb**), four-point
   determinant identity in `Cl(0, 4)`, the biquaternion 6-bivector square law
   `(d + ω₄ m)² = -(d² + m²) - 2 (d ⬝ᵥ m) ω₄` vanishing pseudoscalar iff `kleinQ = 0` (**Bridge VIb**),
   and Gauss's 2-unit complex algebra (`p. 354`).
-/

noncomputable section

namespace InfoGeometry.Clifford.CliffordExtensiveRotorsAndBiquaternions

open Matrix CliffordAlgebra
open InfoGeometry.Projective.PluckerAffineScrew
open InfoGeometry.Projective.KleinQuadricPlucker
open InfoGeometry.Erlangen.ErlangenProgramCurvatureBinaryAndMasterAtlas

section CoreCliffordCarrier

/-- Negative-unit quadratic form `Q(v) = - ∑ i, (v i)²` matching Clifford's `ι_r² = -1`
(`p. 352, 354`). -/
def cliffordNegSqForm (R : Type*) [CommRing R] (n : ℕ) : QuadraticForm R (Fin n → R) :=
  -∑ i : Fin n, QuadraticMap.sq.comp (LinearMap.proj i)

@[simp]
theorem cliffordNegSqForm_apply {R : Type*} [CommRing R] {n : ℕ} (v : Fin n → R) :
    cliffordNegSqForm R n v = -∑ i : Fin n, v i * v i := by
  unfold cliffordNegSqForm
  rw [_root_.neg_apply, _root_.sum_apply]
  simp [QuadraticMap.sq_apply]

theorem cliffordNegSqForm_polar {R : Type*} [CommRing R] {n : ℕ} (u v : Fin n → R) :
    QuadraticMap.polar (cliffordNegSqForm R n) u v = -((2 : R) * (u ⬝ᵥ v)) := by
  simp only [QuadraticMap.polar, cliffordNegSqForm_apply, Pi.add_apply, dotProduct]
  have hsub :
      (-∑ i : Fin n, (u i + v i) * (u i + v i)) - (-∑ i : Fin n, u i * u i) -
          (-∑ i : Fin n, v i * v i) =
        (∑ i : Fin n, u i * u i) + (∑ i : Fin n, v i * v i) -
          ∑ i : Fin n, (u i + v i) * (u i + v i) := by
    ring
  rw [hsub]
  calc
    (∑ i : Fin n, u i * u i) + (∑ i : Fin n, v i * v i) -
        ∑ i : Fin n, (u i + v i) * (u i + v i)
        = ∑ i : Fin n, (u i * u i + v i * v i - (u i + v i) * (u i + v i)) := by
          rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    _ = ∑ i : Fin n, -((2 : R) * (u i * v i)) := by
          refine Finset.sum_congr rfl fun i _ => by ring
    _ = -((2 : R) * ∑ i : Fin n, u i * v i) := by
          rw [Finset.sum_neg_distrib, ← Finset.mul_sum]

/-- The `r`-th elementary Clifford unit `ι_r` (`p. 351`). -/
def cGen (R : Type*) [CommRing R] (n : ℕ) (r : Fin n) :
    CliffordAlgebra (cliffordNegSqForm R n) :=
  ι (cliffordNegSqForm R n) (Pi.single r (1 : R))

@[simp]
theorem cGen_sq (R : Type*) [CommRing R] (n : ℕ) (r : Fin n) :
    cGen R n r * cGen R n r = -1 := by
  rw [cGen, ι_sq_scalar, cliffordNegSqForm_apply]
  have hsum : ∑ i : Fin n, (Pi.single r (1 : R) : Fin n → R) i *
      (Pi.single r (1 : R) : Fin n → R) i = 1 := by
    simp [Pi.single_apply]
  rw [hsum, map_neg, map_one]

theorem cGen_anticomm {R : Type*} [CommRing R] {n : ℕ} {r s : Fin n} (hrs : r ≠ s) :
    cGen R n r * cGen R n s = -(cGen R n s * cGen R n r) := by
  have hpol : QuadraticMap.polar (cliffordNegSqForm R n)
      (Pi.single r (1 : R)) (Pi.single s (1 : R)) = 0 := by
    rw [cliffordNegSqForm_polar]
    have hdot : (Pi.single r (1 : R) : Fin n → R) ⬝ᵥ (Pi.single s (1 : R) : Fin n → R) = 0 := by
      simp [dotProduct, Pi.single_apply]
      intro h
      exact False.elim (hrs h.symm)
    rw [hdot, mul_zero, neg_zero]
  have hcomm := ι_mul_ι_comm (Pi.single s (1 : R)) (Pi.single r (1 : R))
    (Q := cliffordNegSqForm R n)
  rw [QuadraticMap.polar_comm, hpol, map_zero, zero_sub] at hcomm
  change cGen R n s * cGen R n r = -(cGen R n r * cGen R n s) at hcomm
  rw [hcomm, neg_neg]

theorem cGen_mul_swap {R : Type*} [CommRing R] {n : ℕ} {r s : Fin n} (hrs : r ≠ s) :
    cGen R n r * cGen R n s + cGen R n s * cGen R n r = 0 := by
  rw [cGen_anticomm hrs, neg_add_cancel]

/-- Sorted list of elements in `S : Finset (Fin n)`. -/
def bladeList {n : ℕ} (S : Finset (Fin n)) : List (Fin n) :=
  (List.finRange n).filter (· ∈ S)

theorem bladeList_nodup {n : ℕ} (S : Finset (Fin n)) : (bladeList S).Nodup :=
  (List.nodup_finRange n).filter _

theorem bladeList_pairwise_lt {n : ℕ} (S : Finset (Fin n)) : (bladeList S).Pairwise (· < ·) :=
  (List.pairwise_lt_finRange n).filter _

theorem mem_bladeList {n : ℕ} {S : Finset (Fin n)} {x : Fin n} :
    x ∈ bladeList S ↔ x ∈ S := by
  unfold bladeList
  rw [List.mem_filter]
  exact ⟨fun h => decide_eq_true_eq.mp h.2, fun hx => ⟨List.mem_finRange x, decide_eq_true_eq.mpr hx⟩⟩

theorem bladeList_toFinset {n : ℕ} (S : Finset (Fin n)) : (bladeList S).toFinset = S := by
  ext x; exact (List.mem_toFinset).trans mem_bladeList

theorem bladeList_length {n : ℕ} (S : Finset (Fin n)) :
    (bladeList S).length = S.card := by
  have hperm := List.toFinset_card_of_nodup (bladeList_nodup S)
  rw [bladeList_toFinset S] at hperm
  exact hperm.symm

/-- Ordered Clifford blade `∏_{r ∈ S} ι_r` in ascending index order (`p. 355`). -/
def cBlade (R : Type*) [CommRing R] (n : ℕ) (S : Finset (Fin n)) :
    CliffordAlgebra (cliffordNegSqForm R n) :=
  ((bladeList S).map (cGen R n)).prod

@[simp]
theorem cBlade_empty (R : Type*) [CommRing R] (n : ℕ) :
    cBlade R n ∅ = 1 := by
  simp [cBlade, bladeList]

@[simp]
theorem cBlade_singleton (R : Type*) [CommRing R] (n : ℕ) (r : Fin n) :
    cBlade R n {r} = cGen R n r := by
  have hfilt : (List.finRange n).filter (· ∈ ({r} : Finset (Fin n))) = [r] := by
    have hnd : ((List.finRange n).filter (· ∈ ({r} : Finset (Fin n)))).Nodup :=
      (List.nodup_finRange n).filter _
    have hmem : ∀ x, x ∈ (List.finRange n).filter (· ∈ ({r} : Finset (Fin n))) ↔
        x ∈ ([r] : List (Fin n)) := by
      intro x; simp
    exact List.perm_singleton.mp ((List.perm_ext_iff_of_nodup hnd (List.nodup_singleton r)).mpr hmem)
  rw [cBlade, bladeList, hfilt]
  simp

private def bladeInversionCount {n : ℕ} (r : Fin n) (T : Finset (Fin n)) : ℕ :=
  (T.filter (· < r)).card

private lemma bladeInversionCount_symmDiff {n : ℕ} (r : Fin n) (T : Finset (Fin n)) :
    bladeInversionCount r (symmDiff {r} T) = bladeInversionCount r T := by
  dsimp [bladeInversionCount]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_symmDiff, Finset.mem_singleton]
  by_cases hx : x = r
  · subst hx; simp
  · simp [hx]

private def leftMulSingleFun (R : Type*) [CommRing R] (n : ℕ) (r : Fin n)
    (f : Finset (Fin n) → R) (T : Finset (Fin n)) : R :=
  (((-1 : R) ^ bladeInversionCount r T) * (if r ∈ T then 1 else -1)) * f (symmDiff {r} T)

private def leftMulSingle (R : Type*) [CommRing R] (n : ℕ) (r : Fin n) :
    Module.End R (Finset (Fin n) → R) where
  toFun := leftMulSingleFun R n r
  map_add' f g := by
    ext T; simp [leftMulSingleFun, mul_add]
  map_smul' c f := by
    ext T; simp [leftMulSingleFun]; ring

private lemma leftMulSingle_sq (R : Type*) [CommRing R] (n : ℕ) (r : Fin n) :
    leftMulSingle R n r * leftMulSingle R n r = -1 := by
  refine LinearMap.ext fun f => funext fun T => by
    change leftMulSingleFun R n r (leftMulSingleFun R n r f) T = -f T
    simp only [leftMulSingleFun, bladeInversionCount_symmDiff]
    rw [symmDiff_symmDiff_cancel_left]
    have hmem : r ∈ symmDiff {r} T ↔ r ∉ T := by
      simp [Finset.mem_symmDiff, Finset.mem_singleton]
    by_cases hr : r ∈ T
    · have hr' : r ∉ symmDiff {r} T := fun h => hmem.mp h hr
      simp only [hr, ↓reduceIte, hr', mul_one, mul_neg_one]
      have hpow : (-1 : R) ^ bladeInversionCount r T * (-1 : R) ^ bladeInversionCount r T = 1 := by
        rw [← pow_add, ← two_mul, pow_mul]; simp
      calc
        _ = -(((-1 : R) ^ bladeInversionCount r T * (-1 : R) ^ bladeInversionCount r T) * f T) := by
          ring
        _ = -f T := by rw [hpow, one_mul]
    · have hr' : r ∈ symmDiff {r} T := hmem.mpr hr
      simp only [hr, ↓reduceIte, hr', mul_one, mul_neg_one]
      have hpow : (-1 : R) ^ bladeInversionCount r T * (-1 : R) ^ bladeInversionCount r T = 1 := by
        rw [← pow_add, ← two_mul, pow_mul]; simp
      rw [neg_mul, ← mul_assoc, hpow, one_mul]

private lemma card_filter_lt_symmDiff_of_lt {n : ℕ} {r s : Fin n} (hrs : r < s)
    (T : Finset (Fin n)) :
    (T.filter (· < s)).card + ((symmDiff {s} T).filter (· < r)).card ≡
      (T.filter (· < r)).card + ((symmDiff {r} T).filter (· < s)).card + 1 [MOD 2] := by
  have hs_sym : (symmDiff {s} T).filter (· < r) = T.filter (· < r) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_symmDiff, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨rfl, _⟩ | ⟨hxT, _⟩, hxr⟩
      · exact False.elim (lt_asymm hrs hxr)
      · exact ⟨hxT, hxr⟩
    · rintro ⟨hxT, hxr⟩
      exact ⟨Or.inr ⟨hxT, (lt_trans hxr hrs).ne⟩, hxr⟩
  rw [hs_sym]
  by_cases hrt : r ∈ T
  · have hfilter : (symmDiff {r} T).filter (· < s) = (T.filter (· < s)).erase r := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_symmDiff, Finset.mem_singleton, Finset.mem_erase]
      by_cases hxr : x = r
      · subst hxr; simp [hrt]
      · simp [hxr, and_comm]
    have hmem_s : r ∈ T.filter (· < s) := Finset.mem_filter.mpr ⟨hrt, hrs⟩
    rw [hfilter, Finset.card_erase_of_mem hmem_s]
    have hpos : 0 < (T.filter (· < s)).card := Finset.card_pos.mpr ⟨r, hmem_s⟩
    rw [Nat.ModEq]
    omega
  · have hfilter : (symmDiff {r} T).filter (· < s) = insert r (T.filter (· < s)) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_symmDiff, Finset.mem_singleton, Finset.mem_insert]
      by_cases hxr : x = r
      · subst hxr; simp [hrt, hrs]
      · simp [hxr]
    have hnotmem_s : r ∉ T.filter (· < s) := by simp [Finset.mem_filter, hrt]
    rw [hfilter, Finset.card_insert_of_notMem hnotmem_s]
    rw [Nat.ModEq]
    omega

private lemma neg_one_pow_mod_two {R : Type*} [CommRing R] {a b : ℕ}
    (h : a ≡ b + 1 [MOD 2]) : (-1 : R) ^ a = -((-1 : R) ^ b) := by
  obtain ⟨k, rfl⟩ | ⟨k, rfl⟩ := Nat.even_or_odd a
  · rw [← two_mul, pow_mul]
    have hodd : b % 2 = 1 := by rw [Nat.ModEq] at h; omega
    have hb : (-1 : R) ^ b = -1 := by
      rw [← Nat.div_add_mod b 2, hodd, pow_add, pow_mul]; simp
    simp [hb]
  · rw [pow_add, pow_mul]
    have hev : b % 2 = 0 := by rw [Nat.ModEq] at h; omega
    have hb : (-1 : R) ^ b = 1 := by
      rw [← Nat.div_add_mod b 2, hev, pow_add, pow_mul]; simp
    simp [hb]

lemma neg_one_pow_eq_of_modEq {R : Type*} [CommRing R] {a b : ℕ}
    (h : a ≡ b [MOD 2]) : (-1 : R) ^ a = (-1 : R) ^ b := by
  have ha : a = 2 * (a / 2) + a % 2 := (Nat.div_add_mod a 2).symm
  have hb : b = 2 * (b / 2) + b % 2 := (Nat.div_add_mod b 2).symm
  rw [Nat.ModEq] at h
  calc
    (-1 : R) ^ a = (-1 : R) ^ (2 * (a / 2) + a % 2) := by nth_rw 1 [ha]
    _ = (-1 : R) ^ (a % 2) := by rw [pow_add, pow_mul]; simp
    _ = (-1 : R) ^ (b % 2) := by rw [h]
    _ = (-1 : R) ^ (2 * (b / 2) + b % 2) := by rw [pow_add, pow_mul]; simp
    _ = (-1 : R) ^ b := by rw [← hb]

private lemma leftMulSingle_anticomm (R : Type*) [CommRing R] (n : ℕ) {r s : Fin n} (hrs : r ≠ s) :
    leftMulSingle R n r * leftMulSingle R n s = -(leftMulSingle R n s * leftMulSingle R n r) := by
  refine LinearMap.ext fun f => funext fun T => by
    change leftMulSingleFun R n r (leftMulSingleFun R n s f) T =
      -leftMulSingleFun R n s (leftMulSingleFun R n r f) T
    simp only [leftMulSingleFun, bladeInversionCount]
    have hsym : symmDiff {s} (symmDiff {r} T) = symmDiff {r} (symmDiff {s} T) := by
      have hcomm_set : symmDiff ({s} : Finset (Fin n)) {r} = symmDiff {r} {s} := symmDiff_comm _ _
      rw [← symmDiff_assoc, hcomm_set, symmDiff_assoc]
    rw [hsym]
    have hmem_rs : (r ∈ symmDiff {s} T ↔ r ∈ T) ∧ (s ∈ symmDiff {r} T ↔ s ∈ T) := by
      simp [Finset.mem_symmDiff, Finset.mem_singleton, hrs, hrs.symm]
    simp only [hmem_rs.1, hmem_rs.2]
    have hmod :
        ((T.filter (· < r)).card + ((symmDiff {r} T).filter (· < s)).card) ≡
          ((T.filter (· < s)).card + ((symmDiff {s} T).filter (· < r)).card) + 1 [MOD 2] ∨
        ((T.filter (· < s)).card + ((symmDiff {s} T).filter (· < r)).card) ≡
          ((T.filter (· < r)).card + ((symmDiff {r} T).filter (· < s)).card) + 1 [MOD 2] := by
      rcases lt_or_gt_of_ne hrs with hlt | hgt
      · exact Or.inr (card_filter_lt_symmDiff_of_lt hlt T)
      · exact Or.inl (card_filter_lt_symmDiff_of_lt hgt T)
    rcases hmod with h1 | h2
    · have hpow := neg_one_pow_mod_two (R := R) h1
      have hpow2 :
          ((-1 : R) ^ (T.filter (· < r)).card) * ((-1 : R) ^ ((symmDiff {r} T).filter (· < s)).card) =
            -(((-1 : R) ^ (T.filter (· < s)).card) * ((-1 : R) ^ ((symmDiff {s} T).filter (· < r)).card)) := by
        rw [← pow_add, ← pow_add]; exact hpow
      calc
        _ = (((-1 : R) ^ (T.filter (· < r)).card) * ((-1 : R) ^ ((symmDiff {r} T).filter (· < s)).card)) *
              ((if r ∈ T then (1 : R) else -1) * (if s ∈ T then (1 : R) else -1) *
                f (symmDiff {r} (symmDiff {s} T))) := by ring
        _ = -((((-1 : R) ^ (T.filter (· < s)).card) * ((-1 : R) ^ ((symmDiff {s} T).filter (· < r)).card)) *
              ((if r ∈ T then (1 : R) else -1) * (if s ∈ T then (1 : R) else -1) *
                f (symmDiff {r} (symmDiff {s} T)))) := by rw [hpow2, neg_mul]
        _ = _ := by ring
    · have hpow := neg_one_pow_mod_two (R := R) h2
      have hpow2 :
          ((-1 : R) ^ (T.filter (· < s)).card) * ((-1 : R) ^ ((symmDiff {s} T).filter (· < r)).card) =
            -(((-1 : R) ^ (T.filter (· < r)).card) * ((-1 : R) ^ ((symmDiff {r} T).filter (· < s)).card)) := by
        rw [← pow_add, ← pow_add]; exact hpow
      have hpow2' :
          ((-1 : R) ^ (T.filter (· < r)).card) * ((-1 : R) ^ ((symmDiff {r} T).filter (· < s)).card) =
            -(((-1 : R) ^ (T.filter (· < s)).card) * ((-1 : R) ^ ((symmDiff {s} T).filter (· < r)).card)) := by
        linear_combination hpow2
      calc
        _ = (((-1 : R) ^ (T.filter (· < r)).card) * ((-1 : R) ^ ((symmDiff {r} T).filter (· < s)).card)) *
              ((if r ∈ T then (1 : R) else -1) * (if s ∈ T then (1 : R) else -1) *
                f (symmDiff {r} (symmDiff {s} T))) := by ring
        _ = -((((-1 : R) ^ (T.filter (· < s)).card) * ((-1 : R) ^ ((symmDiff {s} T).filter (· < r)).card)) *
              ((if r ∈ T then (1 : R) else -1) * (if s ∈ T then (1 : R) else -1) *
                f (symmDiff {r} (symmDiff {s} T)))) := by rw [hpow2', neg_mul]
        _ = _ := by ring

private lemma double_sum_diag_add_lt {M : Type*} [AddCommMonoid M] (n : ℕ) (f : Fin n → Fin n → M) :
    ∑ i : Fin n, ∑ j : Fin n, f i j =
      (∑ i : Fin n, f i i) +
        ∑ i : Fin n, ∑ j ∈ Finset.univ.filter (i < ·), (f i j + f j i) := by
  have hsplit_inner : ∀ i : Fin n,
      ∑ j : Fin n, f i j =
        f i i + (∑ j ∈ Finset.univ.filter (i < ·), f i j) +
          (∑ j ∈ Finset.univ.filter (· < i), f i j) := by
    intro i
    have hu : (Finset.univ : Finset (Fin n)) =
        insert i (Finset.univ.filter (i < ·) ∪ Finset.univ.filter (· < i)) := by
      ext j
      simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_union, Finset.mem_filter,
        true_and, true_iff]
      rcases lt_trichotomy i j with hij | rfl | hji
      · exact Or.inr (Or.inl hij)
      · exact Or.inl rfl
      · exact Or.inr (Or.inr hji)
    have hdisj1 : i ∉ Finset.univ.filter (i < ·) ∪ Finset.univ.filter (· < i) := by
      simp
    have hdisj2 : Disjoint (Finset.univ.filter (i < ·)) (Finset.univ.filter (· < i)) := by
      rw [Finset.disjoint_left]
      intro j hj1 hj2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj1 hj2
      exact lt_asymm hj1 hj2
    nth_rw 1 [hu]
    rw [Finset.sum_insert hdisj1, Finset.sum_union hdisj2]
    abel
  simp_rw [hsplit_inner, Finset.sum_add_distrib]
  have hswap : ∑ i : Fin n, ∑ j ∈ Finset.univ.filter (· < i), f i j =
      ∑ i : Fin n, ∑ j ∈ Finset.univ.filter (i < ·), f j i := by
    simp only [Finset.sum_filter]
    exact Finset.sum_comm
  have hinner :
      (∑ i : Fin n, ∑ j ∈ Finset.univ.filter (i < ·), f i j) +
        (∑ i : Fin n, ∑ j ∈ Finset.univ.filter (i < ·), f j i) =
      ∑ i : Fin n, ∑ j ∈ Finset.univ.filter (i < ·), (f i j + f j i) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => (Finset.sum_add_distrib).symm
  rw [hswap, add_assoc, hinner]

/-- Faithful algebra representation `Cl(0, n) →ₐ End(Finset (Fin n) → R)` over any commutative
ring (no characteristic-2 assumption needed via strict upper-triangular `i < j` pairing). -/
def cliffordEndRep (R : Type*) [CommRing R] (n : ℕ) :
    CliffordAlgebra (cliffordNegSqForm R n) →ₐ[R] Module.End R (Finset (Fin n) → R) :=
  CliffordAlgebra.lift (cliffordNegSqForm R n)
    ⟨{ toFun := fun v => ∑ i : Fin n, v i • leftMulSingle R n i
       map_add' := fun u v => by simp [add_smul, Finset.sum_add_distrib]
       map_smul' := fun c v => by simp [smul_smul, Finset.smul_sum] },
      fun v => by
        dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
        rw [Finset.sum_mul]
        simp_rw [Finset.mul_sum, smul_mul_smul_comm]
        rw [double_sum_diag_add_lt n (fun i j => (v i * v j) • (leftMulSingle R n i * leftMulSingle R n j))]
        have hoff : ∀ i : Fin n, ∀ j ∈ Finset.univ.filter (i < ·),
            (v i * v j) • (leftMulSingle R n i * leftMulSingle R n j) +
              (v j * v i) • (leftMulSingle R n j * leftMulSingle R n i) = 0 := by
          intro i j hj
          have hij : i < j := (Finset.mem_filter.mp hj).2
          rw [leftMulSingle_anticomm R n hij.ne', mul_comm (v j) (v i), smul_neg, add_neg_cancel]
        have hzero : ∑ i : Fin n, ∑ j ∈ Finset.univ.filter (i < ·),
            ((v i * v j) • (leftMulSingle R n i * leftMulSingle R n j) +
              (v j * v i) • (leftMulSingle R n j * leftMulSingle R n i)) = 0 :=
          Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j hj => hoff i j hj
        rw [hzero, add_zero]
        have hdiag : ∑ i : Fin n, (v i * v i) • (leftMulSingle R n i * leftMulSingle R n i) =
            -(∑ i : Fin n, v i * v i) • (1 : Module.End R (Finset (Fin n) → R)) := by
          simp_rw [leftMulSingle_sq, smul_neg, Finset.sum_neg_distrib, ← Finset.sum_smul]
          rw [← neg_smul]
        rw [hdiag, cliffordNegSqForm_apply, Algebra.algebraMap_eq_smul_one]⟩

@[simp]
theorem cliffordEndRep_cGen (R : Type*) [CommRing R] (n : ℕ) (r : Fin n) :
    cliffordEndRep R n (cGen R n r) = leftMulSingle R n r := by
  unfold cliffordEndRep cGen
  rw [CliffordAlgebra.lift_ι_apply, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_eq_single r]
  · simp
  · intro i _ hi
    simp [hi]
  · intro h
    exact False.elim (h (Finset.mem_univ r))

/-- Constructive coordinate readout of `X : Cl(0, n)` in the sorted blade basis `Finset (Fin n) → R`. -/
def bladeRepr (R : Type*) [CommRing R] (n : ℕ)
    (X : CliffordAlgebra (cliffordNegSqForm R n)) : Finset (Fin n) → R :=
  cliffordEndRep R n X (Pi.single (∅ : Finset (Fin n)) (1 : R))

private lemma leftMulSingle_pi_single_of_lt {R : Type*} [CommRing R] {n : ℕ} {r : Fin n}
    {S : Finset (Fin n)} (hr : ∀ x ∈ S, r < x) :
    leftMulSingle R n r (Pi.single S (1 : R)) = Pi.single (insert r S) (1 : R) := by
  have hr_not : r ∉ S := fun h => (lt_irrefl r) (hr r h)
  have hsym_eq : symmDiff {r} S = insert r S := by
    ext x
    simp only [Finset.mem_symmDiff, Finset.mem_singleton, Finset.mem_insert]
    by_cases hx : x = r
    · subst hx; simp [hr_not]
    · simp [hx]
  ext T
  change leftMulSingleFun R n r (Pi.single S (1 : R)) T =
    (Pi.single (insert r S) (1 : R) : Finset (Fin n) → R) T
  simp only [leftMulSingleFun]
  by_cases hT : T = insert r S
  · subst hT
    have hinv : bladeInversionCount r (insert r S) = 0 := by
      dsimp [bladeInversionCount]
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro x hx hxr
      simp only [Finset.mem_insert] at hx
      rcases hx with rfl | hxS
      · exact lt_irrefl _ hxr
      · exact lt_asymm (hr x hxS) hxr
    have hback : symmDiff {r} (insert r S) = S := by
      rw [← hsym_eq, symmDiff_symmDiff_cancel_left]
    simp [hinv, hback]
  · have hne : symmDiff {r} T ≠ S := by
      intro heq
      apply hT
      calc
        T = symmDiff {r} (symmDiff {r} T) := (symmDiff_symmDiff_cancel_left {r} T).symm
        _ = symmDiff {r} S := by rw [heq]
        _ = insert r S := hsym_eq
    simp [hne, hT]

private lemma prod_leftMulSingle_pairwise {R : Type*} [CommRing R] {n : ℕ} :
    ∀ L : List (Fin n), L.Pairwise (· < ·) →
      ((L.map (leftMulSingle R n)).prod) (Pi.single (∅ : Finset (Fin n)) (1 : R)) =
        Pi.single L.toFinset (1 : R)
  | [], _ => by simp
  | a :: tl, h => by
      have ha : ∀ x ∈ tl, a < x := (List.pairwise_cons.mp h).1
      have htl : tl.Pairwise (· < ·) := (List.pairwise_cons.mp h).2
      have ih := prod_leftMulSingle_pairwise (R := R) tl htl
      have haS : ∀ x ∈ tl.toFinset, a < x := fun x hx => ha x (List.mem_toFinset.mp hx)
      rw [List.map_cons, List.prod_cons, Module.End.mul_apply, ih,
        leftMulSingle_pi_single_of_lt haS]
      simp

/-- Every ordered blade `cBlade R n S` has unit coordinate `1` at `S` and `0` elsewhere (`p. 355`). -/
theorem bladeRepr_cBlade (R : Type*) [CommRing R] (n : ℕ) (S : Finset (Fin n)) :
    bladeRepr R n (cBlade R n S) = Pi.single S (1 : R) := by
  have hmap : cliffordEndRep R n (cBlade R n S) =
      ((bladeList S).map (leftMulSingle R n)).prod := by
    simp only [cBlade, map_list_prod, List.map_map, Function.comp_def, cliffordEndRep_cGen]
  rw [bladeRepr, hmap, prod_leftMulSingle_pairwise (bladeList S) (bladeList_pairwise_lt S),
    bladeList_toFinset S]

theorem cBlade_injective (R : Type*) [CommRing R] [Nontrivial R] (n : ℕ) :
    Function.Injective (cBlade R n) := by
  intro S T h
  have hrep := congrArg (bladeRepr R n) h
  rw [bladeRepr_cBlade, bladeRepr_cBlade] at hrep
  have hval := congrFun hrep S
  by_contra hne
  simp [hne] at hval

theorem cBlade_ne_zero (R : Type*) [CommRing R] [Nontrivial R] (n : ℕ) (S : Finset (Fin n)) :
    cBlade R n S ≠ 0 := by
  intro h
  have hrep := congrFun (congrArg (bladeRepr R n) h) S
  dsimp only [bladeRepr] at hrep
  rw [map_zero, LinearMap.zero_apply, Pi.zero_apply] at hrep
  change bladeRepr R n (cBlade R n S) S = 0 at hrep
  rw [bladeRepr_cBlade] at hrep
  simp at hrep

/-- Genuine noncommutativity of generators `ι_r, ι_s` (`r ≠ s`) whenever `(2 : R) ≠ 0` (`p. 351`). -/
theorem cGen_noncomm (R : Type*) [CommRing R] (h2 : (2 : R) ≠ 0) {n : ℕ} {r s : Fin n}
    (hrs : r ≠ s) :
    cGen R n r * cGen R n s ≠ cGen R n s * cGen R n r := by
  intro heq
  rw [cGen_anticomm hrs] at heq
  have hsum : cGen R n s * cGen R n r + cGen R n s * cGen R n r = 0 := by
    calc
      cGen R n s * cGen R n r + cGen R n s * cGen R n r
          = -(cGen R n s * cGen R n r) + cGen R n s * cGen R n r := by nth_rw 1 [heq]
      _ = 0 := neg_add_cancel _
  have hrep := congrArg (fun X => bladeRepr R n X {r, s}) hsum
  dsimp only [bladeRepr] at hrep
  rw [map_add, LinearMap.add_apply, Pi.add_apply, map_zero, LinearMap.zero_apply,
    Pi.zero_apply] at hrep
  change bladeRepr R n (cGen R n s * cGen R n r) {r, s} +
      bladeRepr R n (cGen R n s * cGen R n r) {r, s} = 0 at hrep
  rcases lt_or_gt_of_ne hrs with hlt | hgt
  · have hb : cGen R n r * cGen R n s = cBlade R n {r, s} := by
      have hlist : bladeList ({r, s} : Finset (Fin n)) = [r, s] := by
        have hlen : (bladeList ({r, s} : Finset (Fin n))).length = 2 := by
          rw [bladeList_length, Finset.card_pair hrs]
        have hpw := bladeList_pairwise_lt ({r, s} : Finset (Fin n))
        rcases hL : bladeList ({r, s} : Finset (Fin n)) with _ | ⟨a, _ | ⟨b, _ | ⟨c, tl⟩⟩⟩
        · simp [hL] at hlen
        · simp [hL] at hlen
        · rw [hL] at hpw
          have hab : a < b := (List.pairwise_cons.mp hpw).1 b (by simp)
          have ha : a ∈ ({r, s} : Finset (Fin n)) := mem_bladeList.mp (by rw [hL]; simp)
          have hb' : b ∈ ({r, s} : Finset (Fin n)) := mem_bladeList.mp (by rw [hL]; simp)
          simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb'
          rcases ha with rfl | rfl <;> rcases hb' with rfl | rfl
          · exact False.elim (lt_irrefl _ hab)
          · rfl
          · exact False.elim (lt_irrefl _ (lt_trans hlt hab))
          · exact False.elim (lt_irrefl _ hab)
        · simp [hL] at hlen
      simp [cBlade, hlist]
    have hs : cGen R n s * cGen R n r = -cBlade R n {r, s} := by
      rw [← hb, cGen_anticomm hrs.symm]
    have heval : bladeRepr R n (cGen R n s * cGen R n r) {r, s} = -1 := by
      rw [hs, bladeRepr, map_neg, LinearMap.neg_apply, Pi.neg_apply]
      change -(bladeRepr R n (cBlade R n {r, s}) {r, s}) = -1
      rw [bladeRepr_cBlade]; simp
    rw [heval] at hrep
    apply h2
    linear_combination -hrep
  · have hb : cGen R n s * cGen R n r = cBlade R n {r, s} := by
      have hlist : bladeList ({r, s} : Finset (Fin n)) = [s, r] := by
        have hlen : (bladeList ({r, s} : Finset (Fin n))).length = 2 := by
          rw [bladeList_length, Finset.card_pair hrs]
        have hpw := bladeList_pairwise_lt ({r, s} : Finset (Fin n))
        rcases hL : bladeList ({r, s} : Finset (Fin n)) with _ | ⟨a, _ | ⟨b, _ | ⟨c, tl⟩⟩⟩
        · simp [hL] at hlen
        · simp [hL] at hlen
        · rw [hL] at hpw
          have hab : a < b := (List.pairwise_cons.mp hpw).1 b (by simp)
          have ha : a ∈ ({r, s} : Finset (Fin n)) := mem_bladeList.mp (by rw [hL]; simp)
          have hb' : b ∈ ({r, s} : Finset (Fin n)) := mem_bladeList.mp (by rw [hL]; simp)
          simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb'
          rcases ha with rfl | rfl <;> rcases hb' with rfl | rfl
          · exact False.elim (lt_irrefl _ hab)
          · exact False.elim (lt_irrefl _ (lt_trans hgt hab))
          · rfl
          · exact False.elim (lt_irrefl _ hab)
        · simp [hL] at hlen
      simp [cBlade, hlist]
    have heval : bladeRepr R n (cGen R n s * cGen R n r) {r, s} = 1 := by
      rw [hb, bladeRepr_cBlade]; simp
    rw [heval] at hrep
    apply h2
    linear_combination hrep

/-- Closed real noncommutativity witness for elementary Clifford units `ι₀, ι₁` in `Cl(0, 4)`. -/
theorem cGen4_noncomm_witness : ¬ Commute (cGen ℝ 4 0) (cGen ℝ 4 1) := by
  intro hc
  exact cGen_noncomm ℝ two_ne_zero (by decide) hc

end CoreCliffordCarrier

section Sec3GeneralSignAndOverlapLaws

private lemma cGen_mul_listProd_of_nodup (R : Type*) [CommRing R] (n : ℕ) (r : Fin n) :
    ∀ L : List (Fin n), L.Nodup →
      cGen R n r * ((L.map (cGen R n)).prod) =
        ((-1 : R) ^ (L.length + if r ∈ L then 1 else 0)) •
          (((L.map (cGen R n)).prod) * cGen R n r)
  | [], _ => by simp
  | a :: tl, hnd => by
      have ha_not : a ∉ tl := (List.nodup_cons.mp hnd).1
      have htl : tl.Nodup := (List.nodup_cons.mp hnd).2
      have ih := cGen_mul_listProd_of_nodup R n r tl htl
      by_cases hra : r = a
      · subst hra
        have hnot : r ∉ tl := ha_not
        have ih' : cGen R n r * ((tl.map (cGen R n)).prod) =
            ((-1 : R) ^ tl.length) • (((tl.map (cGen R n)).prod) * cGen R n r) := by
          simpa [hnot] using ih
        have hmod : tl.length + 2 ≡ tl.length [MOD 2] := by
          rw [Nat.ModEq]; omega
        have hpow : ((-1 : R) ^ (tl.length + 2)) = (-1 : R) ^ tl.length :=
          neg_one_pow_eq_of_modEq hmod
        have hid : cGen R n r * (((cGen R n r :: tl.map (cGen R n)).prod)) =
            ((-1 : R) ^ tl.length) • (((cGen R n r :: tl.map (cGen R n)).prod) * cGen R n r) := by
          calc
            cGen R n r * (((cGen R n r :: tl.map (cGen R n)).prod))
                = cGen R n r * (cGen R n r * ((tl.map (cGen R n)).prod)) := by
                  simp only [List.prod_cons]
            _ = cGen R n r * (((-1 : R) ^ tl.length) • (((tl.map (cGen R n)).prod) * cGen R n r)) := by
                  rw [ih']
            _ = ((-1 : R) ^ tl.length) • ((cGen R n r * ((tl.map (cGen R n)).prod)) * cGen R n r) := by
                  rw [mul_smul_comm, mul_assoc]
            _ = ((-1 : R) ^ tl.length) • (((cGen R n r :: tl.map (cGen R n)).prod) * cGen R n r) := by
                  simp only [List.prod_cons]
        simpa [hpow] using hid
      · have hcomm := cGen_anticomm (R := R) hra
        have hmem_iff : (r ∈ a :: tl) ↔ r ∈ tl := by simp [hra]
        calc
          cGen R n r * ((cGen R n a :: tl.map (cGen R n)).prod)
              = (cGen R n r * cGen R n a) * ((tl.map (cGen R n)).prod) := by
                simp [List.prod_cons, mul_assoc]
          _ = -(cGen R n a * cGen R n r) * ((tl.map (cGen R n)).prod) := by rw [hcomm]
          _ = -(cGen R n a * (cGen R n r * ((tl.map (cGen R n)).prod))) := by noncomm_ring
          _ = -(cGen R n a * ((-1 : R) ^ (tl.length + if r ∈ tl then 1 else 0) •
                (((tl.map (cGen R n)).prod) * cGen R n r))) := by rw [ih]
          _ = ((-1 : R) ^ (tl.length + 1 + if r ∈ a :: tl then 1 else 0)) •
                (((cGen R n a :: tl.map (cGen R n)).prod) * cGen R n r) := by
                simp only [hmem_iff]
                have hexp : tl.length + 1 + (if r ∈ tl then 1 else 0) =
                    (tl.length + if r ∈ tl then 1 else 0) + 1 := by ring
                rw [hexp, pow_succ, mul_neg_one, neg_smul, List.prod_cons]
                simp only [mul_smul_comm, mul_assoc]

/-- Swapping a single generator `ι_r` past a canonical blade `cBlade S` gives `(-1)^(|S| + [r∈S])` (`p. 355`). -/
theorem cGen_mul_cBlade (R : Type*) [CommRing R] (n : ℕ) (r : Fin n) (S : Finset (Fin n)) :
    cGen R n r * cBlade R n S =
      ((-1 : R) ^ (S.card + if r ∈ S then 1 else 0)) • (cBlade R n S * cGen R n r) := by
  have h := cGen_mul_listProd_of_nodup R n r (bladeList S) (bladeList_nodup S)
  simpa [cBlade, bladeList_length, mem_bladeList] using h

private lemma listProd_mul_swap_aux (R : Type*) [CommRing R] (n : ℕ) (L : List (Fin n))
    (hL : L.Nodup) :
    ∀ K : List (Fin n), K.Nodup →
      ((K.map (cGen R n)).prod) * ((L.map (cGen R n)).prod) =
        ((-1 : R) ^ (K.length * L.length + (K.toFinset ∩ L.toFinset).card)) •
          (((L.map (cGen R n)).prod) * ((K.map (cGen R n)).prod))
  | [], _ => by simp
  | a :: tl, hK => by
      have ha_not : a ∉ tl := (List.nodup_cons.mp hK).1
      have htl : tl.Nodup := (List.nodup_cons.mp hK).2
      have ih := listProd_mul_swap_aux R n L hL tl htl
      have hmove := cGen_mul_listProd_of_nodup R n a L hL
      have hcard_inter :
          ((insert a tl.toFinset) ∩ L.toFinset).card =
            (tl.toFinset ∩ L.toFinset).card + (if a ∈ L then 1 else 0) := by
        by_cases haL : a ∈ L
        · have haL' : a ∈ L.toFinset := List.mem_toFinset.mpr haL
          have hnot_inter : a ∉ tl.toFinset ∩ L.toFinset := by
            simp [List.mem_toFinset, ha_not]
          have hins : (insert a tl.toFinset) ∩ L.toFinset =
              insert a (tl.toFinset ∩ L.toFinset) := by
            ext x; simp [haL']
          simp [haL, hins, Finset.card_insert_of_notMem hnot_inter]
        · have haL' : a ∉ L.toFinset := fun h => haL (List.mem_toFinset.mp h)
          have heq : (insert a tl.toFinset) ∩ L.toFinset = tl.toFinset ∩ L.toFinset := by
            ext x; simp only [Finset.mem_inter, Finset.mem_insert]
            constructor
            · rintro ⟨rfl | hxt, hxL⟩
              · exact False.elim (haL' hxL)
              · exact ⟨hxt, hxL⟩
            · rintro ⟨hxt, hxL⟩; exact ⟨Or.inr hxt, hxL⟩
          simp [haL, heq]
      calc
        ((a :: tl).map (cGen R n)).prod * ((L.map (cGen R n)).prod)
            = cGen R n a * (((tl.map (cGen R n)).prod) * ((L.map (cGen R n)).prod)) := by
              simp [List.prod_cons, mul_assoc]
        _ = ((-1 : R) ^ (tl.length * L.length + (tl.toFinset ∩ L.toFinset).card)) •
              ((cGen R n a * ((L.map (cGen R n)).prod)) * ((tl.map (cGen R n)).prod)) := by
              rw [ih, mul_smul_comm, mul_assoc]
        _ = ((-1 : R) ^ ((a :: tl).length * L.length + ((a :: tl).toFinset ∩ L.toFinset).card)) •
              (((L.map (cGen R n)).prod) * (((a :: tl).map (cGen R n)).prod)) := by
              rw [hmove, smul_mul_assoc, smul_smul, ← pow_add]
              simp only [List.toFinset_cons, hcard_inter, List.length_cons, add_mul, one_mul,
                List.map_cons, List.prod_cons, ← mul_assoc]
              congr 2
              ring

private lemma inter_card_sq_le_mul_card {α : Type*} [DecidableEq α] (S T : Finset α) :
    (S ∩ T).card ^ 2 ≤ S.card * T.card := by
  rw [pow_two]
  exact Nat.mul_le_mul
    (Finset.card_le_card Finset.inter_subset_left)
    (Finset.card_le_card Finset.inter_subset_right)

/-- Clifford's general blade commutation law (`p. 355`):
multiplying a form `P` of order `m = S.card` by `Q` of order `p = T.card` having `k = (S ∩ T).card`
common factors gives `cBlade S * cBlade T = (-1)^(m*p - k^2) • (cBlade T * cBlade S)` (with `k^2 ≤ m*p`). -/
theorem cBlade_mul_swap_overlap (R : Type*) [CommRing R] (n : ℕ) (S T : Finset (Fin n)) :
    (S ∩ T).card ^ 2 ≤ S.card * T.card ∧
      cBlade R n S * cBlade R n T =
        ((-1 : R) ^ (S.card * T.card - (S ∩ T).card ^ 2)) •
          (cBlade R n T * cBlade R n S) := by
  have hle := inter_card_sq_le_mul_card S T
  refine ⟨hle, ?_⟩
  have hraw := listProd_mul_swap_aux R n (bladeList T) (bladeList_nodup T)
    (bladeList S) (bladeList_nodup S)
  have hmod : S.card * T.card - (S ∩ T).card ^ 2 ≡
      S.card * T.card + (S ∩ T).card [MOD 2] := by
    have hk : (S ∩ T).card ^ 2 + (S ∩ T).card = (S ∩ T).card * ((S ∩ T).card + 1) := by ring
    have heven : 2 ∣ (S ∩ T).card * ((S ∩ T).card + 1) := by
      rcases Nat.even_or_odd (S ∩ T).card with ⟨j, hj⟩ | ⟨j, hj⟩
      · exact ⟨j * ((S ∩ T).card + 1), by rw [hj]; ring⟩
      · exact ⟨(S ∩ T).card * (j + 1), by rw [hj]; ring⟩
    rw [Nat.ModEq]
    omega
  have hpow := neg_one_pow_eq_of_modEq (R := R) hmod
  simpa [cBlade, bladeList_length, bladeList_toFinset, ← hpow] using hraw

/-- Clifford's three commutation corollaries (`p. 355`):
(1) disjoint blades, (2) two even blades, and (3) one blade dividing the other. -/
theorem cBlade_comm_three_corollaries (R : Type*) [CommRing R] (n : ℕ) (S T : Finset (Fin n)) :
    (Disjoint S T → cBlade R n S * cBlade R n T =
      ((-1 : R) ^ (S.card * T.card)) • (cBlade R n T * cBlade R n S)) ∧
    (Even S.card → Even T.card → cBlade R n S * cBlade R n T =
      ((-1 : R) ^ (S ∩ T).card) • (cBlade R n T * cBlade R n S)) ∧
    (S ⊆ T → cBlade R n S * cBlade R n T =
      ((-1 : R) ^ (S.card * (T.card - S.card))) • (cBlade R n T * cBlade R n S)) := by
  have hbase := (cBlade_mul_swap_overlap R n S T).2
  have hle := (cBlade_mul_swap_overlap R n S T).1
  refine ⟨?_, ?_, ?_⟩
  · intro hd
    rw [Finset.disjoint_iff_inter_eq_empty.mp hd, Finset.card_empty, zero_pow two_ne_zero,
      tsub_zero] at hbase
    exact hbase
  · intro hS _hT
    have hmul_even : 2 ∣ S.card * T.card := by
      rcases hS with ⟨a, ha⟩
      exact ⟨a * T.card, by rw [ha]; ring⟩
    have hk_mod : S.card * T.card - (S ∩ T).card ^ 2 ≡ (S ∩ T).card [MOD 2] := by
      have hk : (S ∩ T).card ^ 2 + (S ∩ T).card = (S ∩ T).card * ((S ∩ T).card + 1) := by ring
      have hev2 : 2 ∣ (S ∩ T).card * ((S ∩ T).card + 1) := by
        rcases Nat.even_or_odd (S ∩ T).card with ⟨j, hj⟩ | ⟨j, hj⟩
        · exact ⟨j * ((S ∩ T).card + 1), by rw [hj]; ring⟩
        · exact ⟨(S ∩ T).card * (j + 1), by rw [hj]; ring⟩
      rw [Nat.ModEq]
      omega
    rw [neg_one_pow_eq_of_modEq hk_mod] at hbase
    exact hbase
  · intro hsub
    have hinter : S ∩ T = S := Finset.inter_eq_left.mpr hsub
    have hcard_le : S.card ≤ T.card := Finset.card_le_card hsub
    have heq_exp : S.card * T.card - (S ∩ T).card ^ 2 = S.card * (T.card - S.card) := by
      rw [hinter, pow_two, ← Nat.mul_sub_left_distrib]
    rw [heq_exp] at hbase
    exact hbase

private lemma listProd_sq_of_nodup (R : Type*) [CommRing R] (n : ℕ) :
    ∀ L : List (Fin n), L.Nodup →
      ((L.map (cGen R n)).prod) * ((L.map (cGen R n)).prod) =
        ((-1 : R) ^ (L.length * (L.length + 1) / 2)) • 1
  | [], _ => by simp
  | a :: tl, hnd => by
      have ha_not : a ∉ tl := (List.nodup_cons.mp hnd).1
      have htl : tl.Nodup := (List.nodup_cons.mp hnd).2
      have ih := listProd_sq_of_nodup R n tl htl
      have hswap := cGen_mul_listProd_of_nodup R n a tl htl
      simp [ha_not] at hswap
      have hmove : ((tl.map (cGen R n)).prod) * cGen R n a =
          ((-1 : R) ^ tl.length) • (cGen R n a * ((tl.map (cGen R n)).prod)) := by
        calc
          ((tl.map (cGen R n)).prod) * cGen R n a
              = (((-1 : R) ^ tl.length) * ((-1 : R) ^ tl.length)) •
                  (((tl.map (cGen R n)).prod) * cGen R n a) := by
                have h1 : (-1 : R) ^ tl.length * (-1 : R) ^ tl.length = 1 := by
                  rw [← pow_add, ← two_mul, pow_mul]; simp
                rw [h1, one_smul]
          _ = ((-1 : R) ^ tl.length) • (cGen R n a * ((tl.map (cGen R n)).prod)) := by
                rw [← smul_smul, ← hswap]
      have htri : (tl.length + 1) * (tl.length + 1 + 1) / 2 =
          tl.length * (tl.length + 1) / 2 + (tl.length + 1) := by
        have hsum : 2 * (tl.length * (tl.length + 1) / 2 + (tl.length + 1)) =
            (tl.length + 1) * (tl.length + 1 + 1) := by
          have hdvd : 2 ∣ tl.length * (tl.length + 1) := by
            rcases Nat.even_or_odd tl.length with ⟨j, hj⟩ | ⟨j, hj⟩
            · exact ⟨j * (tl.length + 1), by rw [hj]; ring⟩
            · exact ⟨tl.length * (j + 1), by rw [hj]; ring⟩
          have h2 : 2 * (tl.length * (tl.length + 1) / 2) = tl.length * (tl.length + 1) :=
            Nat.mul_div_cancel' hdvd
          linarith
        omega
      calc
        (((a :: tl).map (cGen R n)).prod) * (((a :: tl).map (cGen R n)).prod)
            = cGen R n a * ((((tl.map (cGen R n)).prod) * cGen R n a) *
                ((tl.map (cGen R n)).prod)) := by
              simp [List.prod_cons, mul_assoc]
        _ = ((-1 : R) ^ tl.length) •
              ((cGen R n a * cGen R n a) *
                (((tl.map (cGen R n)).prod) * ((tl.map (cGen R n)).prod))) := by
              rw [hmove, smul_mul_assoc, mul_smul_comm, mul_assoc, mul_assoc]
        _ = ((-1 : R) ^ tl.length) •
              (-((((tl.map (cGen R n)).prod) * ((tl.map (cGen R n)).prod)))) := by
              rw [cGen_sq, neg_one_mul]
        _ = ((-1 : R) ^ (tl.length * (tl.length + 1) / 2 + (tl.length + 1))) •
              (1 : CliffordAlgebra _) := by
              rw [ih, smul_neg, ← neg_smul, smul_smul]
              congr 1
              rw [pow_add, pow_add, pow_one]
              ring
        _ = ((-1 : R) ^ ((a :: tl).length * ((a :: tl).length + 1) / 2)) • 1 := by
              simp only [List.length_cons, htri]

/-- Clifford's blade-square theorem (`p. 355`):
the square of a term of order `m = S.card` is `(-1)^(m(m+1)/2) • 1`. -/
theorem cBlade_sq (R : Type*) [CommRing R] (n : ℕ) (S : Finset (Fin n)) :
    cBlade R n S * cBlade R n S = ((-1 : R) ^ (S.card * (S.card + 1) / 2)) • 1 := by
  have h := listProd_sq_of_nodup R n (bladeList S) (bladeList_nodup S)
  simpa [cBlade, bladeList_length] using h

/-- Parity lemma: `cBlade R n S` under `involute` picks up `(-1)^(|S|)`. -/
theorem involute_cBlade (R : Type*) [CommRing R] (n : ℕ) (S : Finset (Fin n)) :
    CliffordAlgebra.involute (cBlade R n S) = ((-1 : R) ^ S.card) • cBlade R n S := by
  have hind : ∀ L : List (Fin n),
      CliffordAlgebra.involute ((L.map (cGen R n)).prod) =
        ((-1 : R) ^ L.length) • ((L.map (cGen R n)).prod) := by
    intro L
    induction L with
    | nil => simp
    | cons a tl ih =>
        simp only [List.map_cons, List.prod_cons, map_mul, ih, List.length_cons]
        have hi : CliffordAlgebra.involute (cGen R n a) = -cGen R n a := CliffordAlgebra.involute_ι _
        rw [hi, neg_mul, mul_smul_comm, pow_succ, mul_neg_one, neg_smul]
  simpa [cBlade, bladeList_length] using hind (bladeList S)

/-- Any even-order blade `cBlade R n S` lies in Mathlib's `CliffordAlgebra.even`. -/
theorem cBlade_mem_even (R : Type*) [CommRing R] (n : ℕ) {S : Finset (Fin n)}
    (hS : Even S.card) :
    cBlade R n S ∈ CliffordAlgebra.even (cliffordNegSqForm R n) := by
  rcases hS with ⟨m, hm⟩
  have hlen : (bladeList S).length = m + m := by rw [bladeList_length, hm]
  suffices ∀ (k : ℕ) (L : List (Fin n)), L.length = 2 * k →
      ((L.map (cGen R n)).prod) ∈ CliffordAlgebra.even (cliffordNegSqForm R n) by
    exact this m (bladeList S) (by rw [hlen, two_mul])
  intro k L
  induction k generalizing L with
  | zero =>
      intro h0
      rw [List.length_eq_zero_iff.mp h0]
      simp only [List.map_nil, List.prod_nil]
      exact Subalgebra.one_mem _
  | succ k ih =>
      intro hlen
      rcases L with _ | ⟨a, _ | ⟨b, tl⟩⟩
      · simp at hlen
      · simp at hlen; omega
      · have htl : tl.length = 2 * k := by simp only [List.length_cons] at hlen; omega
        have hmem_pair : cGen R n a * cGen R n b ∈ CliffordAlgebra.even (cliffordNegSqForm R n) := by
          change cGen R n a * cGen R n b ∈
            Subalgebra.toSubmodule (CliffordAlgebra.even (cliffordNegSqForm R n))
          rw [CliffordAlgebra.even_toSubmodule]
          exact CliffordAlgebra.ι_mul_ι_mem_evenOdd_zero _ _ _
        rw [List.map_cons, List.map_cons, List.prod_cons, List.prod_cons, ← mul_assoc]
        exact Subalgebra.mul_mem _ hmem_pair (ih tl htl)

end Sec3GeneralSignAndOverlapLaws

section BridgeVGrassmannToClifford

private def cliffordToExteriorAux [Invertible (2 : ℝ)] (n : ℕ) :
    CliffordAlgebra (cliffordNegSqForm ℝ n) ≃ₗ[ℝ] ExteriorAlgebra ℝ (Fin n → ℝ) :=
  CliffordAlgebra.equivExterior (cliffordNegSqForm ℝ n)

/-- Canonical `ℝ`-linear isomorphism `Cl(0, n) ≃ₗ[ℝ] Λ(ℝⁿ)` (`p. 350`). -/
def cliffordToExterior (n : ℕ) :
    CliffordAlgebra (cliffordNegSqForm ℝ n) ≃ₗ[ℝ] ExteriorAlgebra ℝ (Fin n → ℝ) :=
  @cliffordToExteriorAux ⟨(1 / 2 : ℝ), by norm_num, by norm_num⟩ n

private lemma bridgeV_grassmann_clifford_polar_scalar_aux [Invertible (2 : ℝ)]
    (n : ℕ) (u v : Fin n → ℝ) :
    cliffordToExteriorAux n (ι (cliffordNegSqForm ℝ n) u * ι (cliffordNegSqForm ℝ n) v) =
      ExteriorAlgebra.ι ℝ u * ExteriorAlgebra.ι ℝ v -
        algebraMap ℝ (ExteriorAlgebra ℝ (Fin n → ℝ)) (u ⬝ᵥ v) := by
  have hassoc : (QuadraticMap.associated (R := ℝ) (M := Fin n → ℝ)
      (-cliffordNegSqForm ℝ n)) u v = u ⬝ᵥ v := by
    have hpol : QuadraticMap.polar (-cliffordNegSqForm ℝ n) u v = 2 * (u ⬝ᵥ v) := by
      dsimp only [QuadraticMap.polar]
      change -(cliffordNegSqForm ℝ n (u + v)) - -(cliffordNegSqForm ℝ n u) -
          -(cliffordNegSqForm ℝ n v) = 2 * (u ⬝ᵥ v)
      simp only [cliffordNegSqForm_apply, neg_neg, Pi.add_apply, dotProduct]
      calc
        ∑ i : Fin n, (u i + v i) * (u i + v i) - ∑ i : Fin n, u i * u i -
            ∑ i : Fin n, v i * v i
            = ∑ i : Fin n, ((u i + v i) * (u i + v i) - u i * u i - v i * v i) := by
              rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
        _ = ∑ i : Fin n, 2 * (u i * v i) := by
              refine Finset.sum_congr rfl fun i _ => by ring
        _ = 2 * ∑ i : Fin n, u i * v i := by rw [← Finset.mul_sum]
    rw [QuadraticMap.associated_apply, invOf_smul_eq_iff, two_smul]
    change QuadraticMap.polar (-cliffordNegSqForm ℝ n) u v = u ⬝ᵥ v + u ⬝ᵥ v
    rw [hpol]
    ring
  have hcf := CliffordAlgebra.changeForm_ι_mul_ι
    (CliffordAlgebra.changeForm.associated_neg_proof (Q := cliffordNegSqForm ℝ n)) u v
  change CliffordAlgebra.changeForm
      (CliffordAlgebra.changeForm.associated_neg_proof (Q := cliffordNegSqForm ℝ n))
      (ι (cliffordNegSqForm ℝ n) u * ι (cliffordNegSqForm ℝ n) v) = _
  rw [hcf, hassoc]

/-- **Bridge V (`Grassmann 1862` ↔ `Clifford 1878`, `p. 350`)**:
over `ℝ`, Mathlib's `CliffordAlgebra.equivExterior` links polar Clifford products to
Grassmann's exterior product minus scalar inner contraction:
`cliffordToExterior n (ι u * ι v) = ExteriorAlgebra.ι u * ExteriorAlgebra.ι v - (u ⬝ᵥ v) • 1`. -/
theorem bridgeV_grassmann_clifford_polar_scalar (n : ℕ) (u v : Fin n → ℝ) :
    cliffordToExterior n (ι (cliffordNegSqForm ℝ n) u * ι (cliffordNegSqForm ℝ n) v) =
      ExteriorAlgebra.ι ℝ u * ExteriorAlgebra.ι ℝ v -
        algebraMap ℝ (ExteriorAlgebra ℝ (Fin n → ℝ)) (u ⬝ᵥ v) :=
  @bridgeV_grassmann_clifford_polar_scalar_aux ⟨(1 / 2 : ℝ), by norm_num, by norm_num⟩ n u v

end BridgeVGrassmannToClifford

section Sec1QuaternionsRotorsAndBridgeVIIa

/-- Quaternion versor `i = ι₂ ι₃` in Clifford's 4-unit algebra `Cl(0, 4)` (`p. 352`). -/
def q4I (R : Type*) [CommRing R] : CliffordAlgebra (cliffordNegSqForm R 4) :=
  cGen R 4 2 * cGen R 4 3

/-- Quaternion versor `j = ι₃ ι₁` in `Cl(0, 4)` (`p. 352`). -/
def q4J (R : Type*) [CommRing R] : CliffordAlgebra (cliffordNegSqForm R 4) :=
  cGen R 4 3 * cGen R 4 1

/-- Quaternion versor `k = ι₁ ι₂` in `Cl(0, 4)` (`p. 352`). -/
def q4K (R : Type*) [CommRing R] : CliffordAlgebra (cliffordNegSqForm R 4) :=
  cGen R 4 1 * cGen R 4 2

/-- Coordinate-axis rotor `ι₀ ι_r` (`r : Fin 4`) (`p. 353`). -/
def rotor0 (R : Type*) [CommRing R] (r : Fin 4) :
    CliffordAlgebra (cliffordNegSqForm R 4) :=
  cGen R 4 0 * cGen R 4 r

/-- Quaternion multiplication rules `i² = j² = k² = ijk = -1`, `jk = i`, `ki = j`, `ij = k`
derived from binary Grassmann products in `Cl(0, 4)` (`p. 352`). -/
theorem clifford_cl04_quaternion_relations (R : Type*) [CommRing R] :
    q4I R * q4I R = -1 ∧ q4J R * q4J R = -1 ∧ q4K R * q4K R = -1 ∧
      q4J R * q4K R = q4I R ∧ q4K R * q4I R = q4J R ∧ q4I R * q4J R = q4K R ∧
      q4I R * q4J R * q4K R = -1 := by
  have h21 : cGen R 4 2 * cGen R 4 1 = -(cGen R 4 1 * cGen R 4 2) := cGen_anticomm (by decide)
  have h32 : cGen R 4 3 * cGen R 4 2 = -(cGen R 4 2 * cGen R 4 3) := cGen_anticomm (by decide)
  have h13 : cGen R 4 1 * cGen R 4 3 = -(cGen R 4 3 * cGen R 4 1) := cGen_anticomm (by decide)
  have hsq1 : cGen R 4 1 * cGen R 4 1 = -1 := cGen_sq R 4 1
  have hsq2 : cGen R 4 2 * cGen R 4 2 = -1 := cGen_sq R 4 2
  have hsq3 : cGen R 4 3 * cGen R 4 3 = -1 := cGen_sq R 4 3
  have hi2 : q4I R * q4I R = -1 := by
    calc
      q4I R * q4I R = cGen R 4 2 * (cGen R 4 3 * cGen R 4 2) * cGen R 4 3 := by
        simp only [q4I, mul_assoc]
      _ = cGen R 4 2 * -(cGen R 4 2 * cGen R 4 3) * cGen R 4 3 := by rw [h32]
      _ = -((cGen R 4 2 * cGen R 4 2) * (cGen R 4 3 * cGen R 4 3)) := by noncomm_ring
      _ = -1 := by rw [hsq2, hsq3]; noncomm_ring
  have hj2 : q4J R * q4J R = -1 := by
    calc
      q4J R * q4J R = cGen R 4 3 * (cGen R 4 1 * cGen R 4 3) * cGen R 4 1 := by
        simp only [q4J, mul_assoc]
      _ = cGen R 4 3 * -(cGen R 4 3 * cGen R 4 1) * cGen R 4 1 := by rw [h13]
      _ = -((cGen R 4 3 * cGen R 4 3) * (cGen R 4 1 * cGen R 4 1)) := by noncomm_ring
      _ = -1 := by rw [hsq3, hsq1]; noncomm_ring
  have hk2 : q4K R * q4K R = -1 := by
    calc
      q4K R * q4K R = cGen R 4 1 * (cGen R 4 2 * cGen R 4 1) * cGen R 4 2 := by
        simp only [q4K, mul_assoc]
      _ = cGen R 4 1 * -(cGen R 4 1 * cGen R 4 2) * cGen R 4 2 := by rw [h21]
      _ = -((cGen R 4 1 * cGen R 4 1) * (cGen R 4 2 * cGen R 4 2)) := by noncomm_ring
      _ = -1 := by rw [hsq1, hsq2]; noncomm_ring
  have hjk : q4J R * q4K R = q4I R := by
    calc
      q4J R * q4K R = cGen R 4 3 * (cGen R 4 1 * cGen R 4 1) * cGen R 4 2 := by
        simp only [q4J, q4K, mul_assoc]
      _ = -(cGen R 4 3 * cGen R 4 2) := by rw [hsq1]; noncomm_ring
      _ = q4I R := by rw [q4I, h32, neg_neg]
  have hki : q4K R * q4I R = q4J R := by
    calc
      q4K R * q4I R = cGen R 4 1 * (cGen R 4 2 * cGen R 4 2) * cGen R 4 3 := by
        simp only [q4K, q4I, mul_assoc]
      _ = -(cGen R 4 1 * cGen R 4 3) := by rw [hsq2]; noncomm_ring
      _ = q4J R := by rw [q4J, h13, neg_neg]
  have hij : q4I R * q4J R = q4K R := by
    calc
      q4I R * q4J R = cGen R 4 2 * (cGen R 4 3 * cGen R 4 3) * cGen R 4 1 := by
        simp only [q4I, q4J, mul_assoc]
      _ = -(cGen R 4 2 * cGen R 4 1) := by rw [hsq3]; noncomm_ring
      _ = q4K R := by rw [q4K, h21, neg_neg]
  exact ⟨hi2, hj2, hk2, hjk, hki, hij, by rw [hij, hk2]⟩

/-- Clifford's right-angle versor action on both coordinate rotors `ι₀ ι_r` and axis vectors `ι_r`
(`pp. 351–353`). -/
theorem clifford_versor_action_on_rotors_and_vectors (R : Type*) [CommRing R] :
    (q4I R * rotor0 R 2 = rotor0 R 3 ∧
     q4J R * rotor0 R 3 = rotor0 R 1 ∧
     q4K R * rotor0 R 1 = rotor0 R 2) ∧
    (q4I R * cGen R 4 2 = cGen R 4 3 ∧
     q4J R * cGen R 4 3 = cGen R 4 1 ∧
     q4K R * cGen R 4 1 = cGen R 4 2) := by
  have h01 : cGen R 4 1 * cGen R 4 0 = -(cGen R 4 0 * cGen R 4 1) := cGen_anticomm (by decide)
  have h02 : cGen R 4 2 * cGen R 4 0 = -(cGen R 4 0 * cGen R 4 2) := cGen_anticomm (by decide)
  have h03 : cGen R 4 3 * cGen R 4 0 = -(cGen R 4 0 * cGen R 4 3) := cGen_anticomm (by decide)
  have h23 : cGen R 4 3 * cGen R 4 2 = -(cGen R 4 2 * cGen R 4 3) := cGen_anticomm (by decide)
  have h31 : cGen R 4 1 * cGen R 4 3 = -(cGen R 4 3 * cGen R 4 1) := cGen_anticomm (by decide)
  have h12 : cGen R 4 2 * cGen R 4 1 = -(cGen R 4 1 * cGen R 4 2) := cGen_anticomm (by decide)
  have hsq1 : cGen R 4 1 * cGen R 4 1 = -1 := cGen_sq R 4 1
  have hsq2 : cGen R 4 2 * cGen R 4 2 = -1 := cGen_sq R 4 2
  have hsq3 : cGen R 4 3 * cGen R 4 3 = -1 := cGen_sq R 4 3
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · calc
      q4I R * rotor0 R 2 = cGen R 4 2 * (cGen R 4 3 * cGen R 4 0) * cGen R 4 2 := by
        simp [q4I, rotor0, mul_assoc]
      _ = -(cGen R 4 2 * (cGen R 4 0 * cGen R 4 3) * cGen R 4 2) := by rw [h03]; noncomm_ring
      _ = cGen R 4 0 * (cGen R 4 2 * cGen R 4 3 * cGen R 4 2) := by
        rw [← mul_assoc (cGen R 4 2), h02]; noncomm_ring
      _ = cGen R 4 0 * cGen R 4 3 := by
        rw [mul_assoc (cGen R 4 2) (cGen R 4 3), h23]
        have hh : -(cGen R 4 2 * cGen R 4 2) * cGen R 4 3 = cGen R 4 3 := by rw [hsq2]; noncomm_ring
        calc
          cGen R 4 0 * (cGen R 4 2 * -(cGen R 4 2 * cGen R 4 3))
              = cGen R 4 0 * (-(cGen R 4 2 * cGen R 4 2) * cGen R 4 3) := by noncomm_ring
          _ = cGen R 4 0 * cGen R 4 3 := by rw [hh]
  · calc
      q4J R * rotor0 R 3 = cGen R 4 3 * (cGen R 4 1 * cGen R 4 0) * cGen R 4 3 := by
        simp [q4J, rotor0, mul_assoc]
      _ = -(cGen R 4 3 * (cGen R 4 0 * cGen R 4 1) * cGen R 4 3) := by rw [h01]; noncomm_ring
      _ = cGen R 4 0 * (cGen R 4 3 * cGen R 4 1 * cGen R 4 3) := by
        rw [← mul_assoc (cGen R 4 3), h03]; noncomm_ring
      _ = cGen R 4 0 * cGen R 4 1 := by
        rw [mul_assoc (cGen R 4 3) (cGen R 4 1), h31]
        have hh : -(cGen R 4 3 * cGen R 4 3) * cGen R 4 1 = cGen R 4 1 := by rw [hsq3]; noncomm_ring
        calc
          cGen R 4 0 * (cGen R 4 3 * -(cGen R 4 3 * cGen R 4 1))
              = cGen R 4 0 * (-(cGen R 4 3 * cGen R 4 3) * cGen R 4 1) := by noncomm_ring
          _ = cGen R 4 0 * cGen R 4 1 := by rw [hh]
  · calc
      q4K R * rotor0 R 1 = cGen R 4 1 * (cGen R 4 2 * cGen R 4 0) * cGen R 4 1 := by
        simp [q4K, rotor0, mul_assoc]
      _ = -(cGen R 4 1 * (cGen R 4 0 * cGen R 4 2) * cGen R 4 1) := by rw [h02]; noncomm_ring
      _ = cGen R 4 0 * (cGen R 4 1 * cGen R 4 2 * cGen R 4 1) := by
        rw [← mul_assoc (cGen R 4 1), h01]; noncomm_ring
      _ = cGen R 4 0 * cGen R 4 2 := by
        rw [mul_assoc (cGen R 4 1) (cGen R 4 2), h12]
        have hh : -(cGen R 4 1 * cGen R 4 1) * cGen R 4 2 = cGen R 4 2 := by rw [hsq1]; noncomm_ring
        calc
          cGen R 4 0 * (cGen R 4 1 * -(cGen R 4 1 * cGen R 4 2))
              = cGen R 4 0 * (-(cGen R 4 1 * cGen R 4 1) * cGen R 4 2) := by noncomm_ring
          _ = cGen R 4 0 * cGen R 4 2 := by rw [hh]
  · calc
      q4I R * cGen R 4 2 = cGen R 4 2 * (cGen R 4 3 * cGen R 4 2) := by simp [q4I, mul_assoc]
      _ = cGen R 4 2 * -(cGen R 4 2 * cGen R 4 3) := by rw [h23]
      _ = -(cGen R 4 2 * cGen R 4 2) * cGen R 4 3 := by noncomm_ring
      _ = cGen R 4 3 := by rw [hsq2]; noncomm_ring
  · calc
      q4J R * cGen R 4 3 = cGen R 4 3 * (cGen R 4 1 * cGen R 4 3) := by simp [q4J, mul_assoc]
      _ = cGen R 4 3 * -(cGen R 4 3 * cGen R 4 1) := by rw [h31]
      _ = -(cGen R 4 3 * cGen R 4 3) * cGen R 4 1 := by noncomm_ring
      _ = cGen R 4 1 := by rw [hsq3]; noncomm_ring
  · calc
      q4K R * cGen R 4 1 = cGen R 4 1 * (cGen R 4 2 * cGen R 4 1) := by simp [q4K, mul_assoc]
      _ = cGen R 4 1 * -(cGen R 4 1 * cGen R 4 2) := by rw [h12]
      _ = -(cGen R 4 1 * cGen R 4 1) * cGen R 4 2 := by noncomm_ring
      _ = cGen R 4 2 := by rw [hsq1]; noncomm_ring

/-- Maxwell force-vs-flow grade distinctness (`pp. 352–353`):
linear vector `ι₀` (force) is distinct from bivector area `ι₁ ι₂` (flow) in `Cl(0, 3)`. -/
theorem maxwell_force_ne_flow (R : Type*) [CommRing R] [Nontrivial R] :
    cGen R 3 0 ≠ cGen R 3 1 * cGen R 3 2 := by
  have h1 : cGen R 3 0 = cBlade R 3 {0} := (cBlade_singleton R 3 0).symm
  have h2 : cGen R 3 1 * cGen R 3 2 = cBlade R 3 {1, 2} := by
    have hlist : bladeList ({1, 2} : Finset (Fin 3)) = [1, 2] := by decide
    simp [cBlade, hlist]
  rw [h1, h2]
  intro h
  have hne : ({0} : Finset (Fin 3)) ≠ {1, 2} := by decide
  exact hne (cBlade_injective R 3 h)

/-- 3D quaternion bivector units `i₃ = ι₁ ι₂`, `j₃ = ι₂ ι₀`, `k₃ = ι₀ ι₁` in `Cl(0, 3)`. -/
def q3I (R : Type*) [CommRing R] : CliffordAlgebra (cliffordNegSqForm R 3) :=
  cGen R 3 1 * cGen R 3 2

def q3J (R : Type*) [CommRing R] : CliffordAlgebra (cliffordNegSqForm R 3) :=
  cGen R 3 2 * cGen R 3 0

def q3K (R : Type*) [CommRing R] : CliffordAlgebra (cliffordNegSqForm R 3) :=
  cGen R 3 0 * cGen R 3 1

/-- Quaternion spinor element `q = q₀ + q₁ i₃ + q₂ j₃ + q₃ k₃` in `Cl(0, 3)`. -/
def spinQuat3 {R : Type*} [CommRing R] (q₀ q₁ q₂ q₃ : R) :
    CliffordAlgebra (cliffordNegSqForm R 3) :=
  q₀ • 1 + q₁ • q3I R + q₂ • q3J R + q₃ • q3K R

theorem reverse_spinQuat3 {R : Type*} [CommRing R] (q₀ q₁ q₂ q₃ : R) :
    CliffordAlgebra.reverse (spinQuat3 q₀ q₁ q₂ q₃) =
      q₀ • 1 - q₁ • q3I R - q₂ • q3J R - q₃ • q3K R := by
  have rev_cGen : ∀ r : Fin 3, CliffordAlgebra.reverse (cGen R 3 r) = cGen R 3 r := fun r =>
    CliffordAlgebra.reverse_ι (Q := cliffordNegSqForm R 3) _
  have hi : CliffordAlgebra.reverse (q3I R) = -(q3I R) := by
    rw [q3I, CliffordAlgebra.reverse.map_mul, rev_cGen, rev_cGen]
    exact cGen_anticomm (by decide)
  have hj : CliffordAlgebra.reverse (q3J R) = -(q3J R) := by
    rw [q3J, CliffordAlgebra.reverse.map_mul, rev_cGen, rev_cGen]
    exact cGen_anticomm (by decide)
  have hk : CliffordAlgebra.reverse (q3K R) = -(q3K R) := by
    rw [q3K, CliffordAlgebra.reverse.map_mul, rev_cGen, rev_cGen]
    exact cGen_anticomm (by decide)
  have h1 : CliffordAlgebra.reverse (1 : CliffordAlgebra (cliffordNegSqForm R 3)) = 1 :=
    CliffordAlgebra.reverse.map_one
  simp only [spinQuat3, map_add, map_smul, h1, hi, hj, hk, smul_neg]
  abel

private lemma cl03_mul_table {R : Type*} [CommRing R] :
    let e₀ := cGen R 3 0
    let e₁ := cGen R 3 1
    let e₂ := cGen R 3 2
    let ω₃ := e₀ * e₁ * e₂
    let i := q3I R
    let j := q3J R
    let k := q3K R
    (i * e₀ = ω₃ ∧ j * e₀ = -e₂ ∧ k * e₀ = e₁) ∧
    (i * e₁ = e₂ ∧ j * e₁ = ω₃ ∧ k * e₁ = -e₀) ∧
    (i * e₂ = -e₁ ∧ j * e₂ = e₀ ∧ k * e₂ = ω₃) ∧
    (e₀ * i = ω₃ ∧ e₀ * j = e₂ ∧ e₀ * k = -e₁) ∧
    (e₁ * i = -e₂ ∧ e₁ * j = ω₃ ∧ e₁ * k = e₀) ∧
    (e₂ * i = e₁ ∧ e₂ * j = -e₀ ∧ e₂ * k = ω₃) ∧
    (ω₃ * i = -e₀ ∧ ω₃ * j = -e₁ ∧ ω₃ * k = -e₂) := by
  dsimp
  have h00 : cGen R 3 0 * cGen R 3 0 = -1 := cGen_sq R 3 0
  have h11 : cGen R 3 1 * cGen R 3 1 = -1 := cGen_sq R 3 1
  have h22 : cGen R 3 2 * cGen R 3 2 = -1 := cGen_sq R 3 2
  have h01 : cGen R 3 0 * cGen R 3 1 = -(cGen R 3 1 * cGen R 3 0) := cGen_anticomm (by decide)
  have h02 : cGen R 3 0 * cGen R 3 2 = -(cGen R 3 2 * cGen R 3 0) := cGen_anticomm (by decide)
  have h10 : cGen R 3 1 * cGen R 3 0 = -(cGen R 3 0 * cGen R 3 1) := cGen_anticomm (by decide)
  have h12 : cGen R 3 1 * cGen R 3 2 = -(cGen R 3 2 * cGen R 3 1) := cGen_anticomm (by decide)
  have h20 : cGen R 3 2 * cGen R 3 0 = -(cGen R 3 0 * cGen R 3 2) := cGen_anticomm (by decide)
  have h21 : cGen R 3 2 * cGen R 3 1 = -(cGen R 3 1 * cGen R 3 2) := cGen_anticomm (by decide)
  have hi : q3I R = cGen R 3 1 * cGen R 3 2 := rfl
  have hj : q3J R = -(cGen R 3 0 * cGen R 3 2) := h20
  have hk : q3K R = cGen R 3 0 * cGen R 3 1 := rfl
  have hii : q3I R * q3I R = -1 := by
    calc q3I R * q3I R = cGen R 3 1 * (cGen R 3 2 * cGen R 3 1) * cGen R 3 2 := by
          simp only [q3I, mul_assoc]
    _ = cGen R 3 1 * -(cGen R 3 1 * cGen R 3 2) * cGen R 3 2 := by rw [h21]
    _ = -((cGen R 3 1 * cGen R 3 1) * (cGen R 3 2 * cGen R 3 2)) := by noncomm_ring
    _ = -1 := by rw [h11, h22]; noncomm_ring
  have hjj : q3J R * q3J R = -1 := by
    calc q3J R * q3J R = (-(cGen R 3 0 * cGen R 3 2)) * (-(cGen R 3 0 * cGen R 3 2)) := by
          rw [hj]
    _ = cGen R 3 0 * (cGen R 3 2 * cGen R 3 0) * cGen R 3 2 := by noncomm_ring
    _ = cGen R 3 0 * -(cGen R 3 0 * cGen R 3 2) * cGen R 3 2 := by rw [h20]
    _ = -((cGen R 3 0 * cGen R 3 0) * (cGen R 3 2 * cGen R 3 2)) := by noncomm_ring
    _ = -1 := by rw [h00, h22]; noncomm_ring
  have hkk : q3K R * q3K R = -1 := by
    calc q3K R * q3K R = cGen R 3 0 * (cGen R 3 1 * cGen R 3 0) * cGen R 3 1 := by
          simp only [q3K, mul_assoc]
    _ = cGen R 3 0 * -(cGen R 3 0 * cGen R 3 1) * cGen R 3 1 := by rw [h10]
    _ = -((cGen R 3 0 * cGen R 3 0) * (cGen R 3 1 * cGen R 3 1)) := by noncomm_ring
    _ = -1 := by rw [h00, h11]; noncomm_ring
  have hω_i : cGen R 3 0 * cGen R 3 1 * cGen R 3 2 = cGen R 3 0 * q3I R := by simp [q3I, mul_assoc]
  have hω_j : cGen R 3 0 * cGen R 3 1 * cGen R 3 2 = cGen R 3 1 * q3J R := by
    rw [hj]; calc
      cGen R 3 0 * cGen R 3 1 * cGen R 3 2
          = -(cGen R 3 1 * cGen R 3 0) * cGen R 3 2 := by rw [h01]
      _ = cGen R 3 1 * -(cGen R 3 0 * cGen R 3 2) := by noncomm_ring
  have hω_k : cGen R 3 0 * cGen R 3 1 * cGen R 3 2 = cGen R 3 2 * q3K R := by
    rw [hk]; calc
      cGen R 3 0 * cGen R 3 1 * cGen R 3 2
          = cGen R 3 0 * -(cGen R 3 2 * cGen R 3 1) := by rw [mul_assoc, h12]
      _ = -(cGen R 3 0 * cGen R 3 2) * cGen R 3 1 := by noncomm_ring
      _ = (cGen R 3 2 * cGen R 3 0) * cGen R 3 1 := by rw [h02, neg_neg]
      _ = cGen R 3 2 * (cGen R 3 0 * cGen R 3 1) := mul_assoc _ _ _
  have hie0 : q3I R * cGen R 3 0 = cGen R 3 0 * cGen R 3 1 * cGen R 3 2 := by
    calc q3I R * cGen R 3 0 = cGen R 3 1 * (cGen R 3 2 * cGen R 3 0) := by simp [q3I, mul_assoc]
    _ = cGen R 3 1 * -(cGen R 3 0 * cGen R 3 2) := by rw [h20]
    _ = -(cGen R 3 1 * cGen R 3 0) * cGen R 3 2 := by noncomm_ring
    _ = cGen R 3 0 * cGen R 3 1 * cGen R 3 2 := by rw [h10]; noncomm_ring
  have hje1 : q3J R * cGen R 3 1 = cGen R 3 0 * cGen R 3 1 * cGen R 3 2 := by
    rw [hj]; calc -(cGen R 3 0 * cGen R 3 2) * cGen R 3 1 = -(cGen R 3 0 * (cGen R 3 2 * cGen R 3 1)) := by noncomm_ring
    _ = cGen R 3 0 * (cGen R 3 1 * cGen R 3 2) := by rw [h21]; noncomm_ring
    _ = cGen R 3 0 * cGen R 3 1 * cGen R 3 2 := (mul_assoc _ _ _).symm
  refine ⟨⟨hie0, ?_, ?_⟩, ⟨?_, hje1, ?_⟩, ⟨?_, ?_, by simp [q3K]⟩, ⟨hω_i.symm, ?_, ?_⟩,
    ⟨?_, hω_j.symm, ?_⟩, ⟨?_, ?_, hω_k.symm⟩, ⟨?_, ?_, ?_⟩⟩
  · rw [hj]
    calc
      -(cGen R 3 0 * cGen R 3 2) * cGen R 3 0
          = cGen R 3 2 * (cGen R 3 0 * cGen R 3 0) := by rw [h02]; noncomm_ring
      _ = -cGen R 3 2 := by rw [h00]; noncomm_ring
  · rw [hk, mul_assoc, h10]; calc cGen R 3 0 * -(cGen R 3 0 * cGen R 3 1) = -(cGen R 3 0 * cGen R 3 0) * cGen R 3 1 := by noncomm_ring
    _ = cGen R 3 1 := by rw [h00]; noncomm_ring
  · rw [hi, mul_assoc, h21]; calc cGen R 3 1 * -(cGen R 3 1 * cGen R 3 2) = -(cGen R 3 1 * cGen R 3 1) * cGen R 3 2 := by noncomm_ring
    _ = cGen R 3 2 := by rw [h11]; noncomm_ring
  · rw [hk, mul_assoc, h11]; noncomm_ring
  · rw [hi, mul_assoc, h22]; noncomm_ring
  · rw [hj, neg_mul, mul_assoc, h22]; noncomm_ring
  · rw [hj, mul_neg, ← mul_assoc, h00]; noncomm_ring
  · rw [hk, ← mul_assoc, h00]; noncomm_ring
  · rw [hi, ← mul_assoc, h11]; noncomm_ring
  · rw [hk, ← mul_assoc, h10]; calc -(cGen R 3 0 * cGen R 3 1) * cGen R 3 1 = -cGen R 3 0 * (cGen R 3 1 * cGen R 3 1) := by noncomm_ring
    _ = cGen R 3 0 := by rw [h11]; noncomm_ring
  · rw [hi, ← mul_assoc, h21]; calc -(cGen R 3 1 * cGen R 3 2) * cGen R 3 2 = -cGen R 3 1 * (cGen R 3 2 * cGen R 3 2) := by noncomm_ring
    _ = cGen R 3 1 := by rw [h22]; noncomm_ring
  · rw [hj, mul_neg, ← mul_assoc, h20]; calc -(-(cGen R 3 0 * cGen R 3 2) * cGen R 3 2) = cGen R 3 0 * (cGen R 3 2 * cGen R 3 2) := by noncomm_ring
    _ = -cGen R 3 0 := by rw [h22]; noncomm_ring
  · rw [hω_i, mul_assoc, hii]; noncomm_ring
  · rw [hω_j, mul_assoc, hjj]; noncomm_ring
  · rw [hω_k, mul_assoc, hkk]; noncomm_ring

private lemma rotor_conj_basis_step {R : Type*} [CommRing R] (q₀ q₁ q₂ q₃ : R) :
    let q := spinQuat3 q₀ q₁ q₂ q₃
    let qrev := CliffordAlgebra.reverse q
    let M := quatRotMatrix q₀ q₁ q₂ q₃
    q * cGen R 3 0 * qrev = M 0 0 • cGen R 3 0 + M 1 0 • cGen R 3 1 + M 2 0 • cGen R 3 2 ∧
    q * cGen R 3 1 * qrev = M 0 1 • cGen R 3 0 + M 1 1 • cGen R 3 1 + M 2 1 • cGen R 3 2 ∧
    q * cGen R 3 2 * qrev = M 0 2 • cGen R 3 0 + M 1 2 • cGen R 3 1 + M 2 2 • cGen R 3 2 := by
  dsimp
  have ht := cl03_mul_table (R := R)
  rcases ht with ⟨⟨hie0, hje0, hke0⟩, ⟨hie1, hje1, hke1⟩, ⟨hie2, hje2, hke2⟩,
    ⟨he0i, he0j, he0k⟩, ⟨he1i, he1j, he1k⟩, ⟨he2i, he2j, he2k⟩, ⟨hωi, hωj, hωk⟩⟩
  rw [reverse_spinQuat3]
  have hleft0 : spinQuat3 q₀ q₁ q₂ q₃ * cGen R 3 0 =
      q₀ • cGen R 3 0 + q₁ • (cGen R 3 0 * cGen R 3 1 * cGen R 3 2) - q₂ • cGen R 3 2 +
        q₃ • cGen R 3 1 := by
    simp only [spinQuat3, add_mul, smul_mul_assoc, one_mul, hie0, hje0, hke0, smul_neg]
    abel
  have hleft1 : spinQuat3 q₀ q₁ q₂ q₃ * cGen R 3 1 =
      q₀ • cGen R 3 1 + q₁ • cGen R 3 2 + q₂ • (cGen R 3 0 * cGen R 3 1 * cGen R 3 2) -
        q₃ • cGen R 3 0 := by
    simp only [spinQuat3, add_mul, smul_mul_assoc, one_mul, hie1, hje1, hke1, smul_neg]
    abel
  have hleft2 : spinQuat3 q₀ q₁ q₂ q₃ * cGen R 3 2 =
      q₀ • cGen R 3 2 - q₁ • cGen R 3 1 + q₂ • cGen R 3 0 +
        q₃ • (cGen R 3 0 * cGen R 3 1 * cGen R 3 2) := by
    simp only [spinQuat3, add_mul, smul_mul_assoc, one_mul, hie2, hje2, hke2, smul_neg]
    abel
  refine ⟨?_, ?_, ?_⟩
  · rw [hleft0]
    simp only [sub_mul, add_mul, mul_sub, mul_smul_comm, smul_mul_assoc, mul_one,
      he0i, he0j, he0k, he1i, he1j, he1k, he2i, he2j, he2k, hωi, hωj, hωk, smul_neg]
    conv_rhs => simp [quatRotMatrix, pow_two]
    module
  · rw [hleft1]
    simp only [sub_mul, add_mul, mul_sub, mul_smul_comm, smul_mul_assoc, mul_one,
      he0i, he0j, he0k, he1i, he1j, he1k, he2i, he2j, he2k, hωi, hωj, hωk, smul_neg]
    conv_rhs => simp [quatRotMatrix, pow_two]
    module
  · rw [hleft2]
    simp only [sub_mul, add_mul, mul_sub, mul_smul_comm, smul_mul_assoc, mul_one,
      he0i, he0j, he0k, he1i, he1j, he1k, he2i, he2j, he2k, hωi, hωj, hωk, smul_neg]
    conv_rhs => simp [quatRotMatrix, pow_two]
    module

/-- **Bridge VIIa (`Clifford 1878 pp. 351–353` ↔ `Klein 1872 Fn. 37 quatRotMatrix`)**:
rotor conjugation `q v q̃` in `Cl(0, 3)` matches the `3 × 3` orthogonal matrix action
`quatRotMatrix q₀ q₁ q₂ q₃ *ᵥ v` identically over any commutative ring `R`. -/
theorem rotor_conjugation_eq_quatRotMatrix {R : Type*} [CommRing R]
    (q₀ q₁ q₂ q₃ : R) (v : Fin 3 → R) :
    let q := spinQuat3 q₀ q₁ q₂ q₃
    q * (∑ a : Fin 3, v a • cGen R 3 a) * CliffordAlgebra.reverse q =
      ∑ a : Fin 3, (quatRotMatrix q₀ q₁ q₂ q₃ *ᵥ v) a • cGen R 3 a := by
  have hsteps := rotor_conj_basis_step q₀ q₁ q₂ q₃
  rcases hsteps with ⟨hs0, hs1, hs2⟩
  dsimp
  simp_rw [Fin.sum_univ_three, mul_add, add_mul, mul_smul_comm, smul_mul_assoc]
  rw [hs0, hs1, hs2]
  simp only [mulVec, dotProduct, Fin.sum_univ_three, Fin.isValue]
  module

end Sec1QuaternionsRotorsAndBridgeVIIa

section Sec2BiquaternionsPolarAndBridgeVIbVIIb

/-- Elliptic 4-unit pseudoscalar `ω = ι₀ ι₁ ι₂ ι₃` (`p. 354`). -/
def ω₄ (R : Type*) [CommRing R] : CliffordAlgebra (cliffordNegSqForm R 4) :=
  cBlade R 4 Finset.univ

theorem ω₄_eq_mul (R : Type*) [CommRing R] :
    ω₄ R = cGen R 4 0 * cGen R 4 1 * cGen R 4 2 * cGen R 4 3 := by
  have hlist : bladeList (Finset.univ : Finset (Fin 4)) = [0, 1, 2, 3] := by decide
  simp [ω₄, cBlade, hlist, mul_assoc]

/-- Polar-polarity involution `ω₄² = 1` (`p. 354`), obtained directly from `cBlade_sq`. -/
theorem ω₄_sq (R : Type*) [CommRing R] : ω₄ R * ω₄ R = 1 := by
  have h := cBlade_sq R 4 Finset.univ
  have hcard : (Finset.univ : Finset (Fin 4)).card = 4 := by decide
  rw [hcard] at h
  norm_num at h
  exact h

/-- **Bridge VIIb (`Clifford 1878 p. 354` ↔ `Klein 1872 Elliptic Polarity`)**:
multiplication by `ω₄` is polar with every point `ι_r` (`ω₄ ι_r = -ι_r ω₄`) and scalar with
every even bivector (`q4I, q4J, q4K`), carrying any point to its polar hyperplane. -/
theorem ω₄_polar_points_scalar_versors (R : Type*) [CommRing R] :
    (∀ r : Fin 4, ω₄ R * cGen R 4 r = -(cGen R 4 r * ω₄ R)) ∧
      (ω₄ R * q4I R = q4I R * ω₄ R ∧
       ω₄ R * q4J R = q4J R * ω₄ R ∧
       ω₄ R * q4K R = q4K R * ω₄ R) := by
  have hω_left : ∀ r : Fin 4, ω₄ R * cGen R 4 r = -(cGen R 4 r * ω₄ R) := by
    intro r
    have h := cGen_mul_cBlade R 4 r Finset.univ
    simp only [Finset.card_fin, Finset.mem_univ, ↓reduceIte] at h
    norm_num at h
    change cGen R 4 r * ω₄ R = -(ω₄ R * cGen R 4 r) at h
    calc
      ω₄ R * cGen R 4 r = -(-(ω₄ R * cGen R 4 r)) := (neg_neg _).symm
      _ = -(cGen R 4 r * ω₄ R) := by rw [← h]
  refine ⟨hω_left, ?_⟩
  have hpair : ∀ (a b : Fin 4), ω₄ R * (cGen R 4 a * cGen R 4 b) =
      (cGen R 4 a * cGen R 4 b) * ω₄ R := by
    intro a b
    have hωa := hω_left a
    have hωb := hω_left b
    calc
      ω₄ R * (cGen R 4 a * cGen R 4 b) = (ω₄ R * cGen R 4 a) * cGen R 4 b := by rw [← mul_assoc]
      _ = -(cGen R 4 a * ω₄ R) * cGen R 4 b := by rw [hωa]
      _ = -(cGen R 4 a * (ω₄ R * cGen R 4 b)) := by noncomm_ring
      _ = -(cGen R 4 a * -(cGen R 4 b * ω₄ R)) := by rw [hωb]
      _ = (cGen R 4 a * cGen R 4 b) * ω₄ R := by noncomm_ring
  exact ⟨hpair 2 3, hpair 3 1, hpair 1 2⟩

private lemma leftMulSingle_card_bound {R : Type*} [CommRing R] {n k : ℕ} {r : Fin n}
    {f : Finset (Fin n) → R} (hf : ∀ U : Finset (Fin n), f U ≠ 0 → U.card ≤ k) :
    ∀ T : Finset (Fin n), leftMulSingle R n r f T ≠ 0 → T.card ≤ k + 1 := by
  intro T hT
  change leftMulSingleFun R n r f T ≠ 0 at hT
  have hf_ne : f (symmDiff {r} T) ≠ 0 := by
    intro hz
    apply hT
    simp [leftMulSingleFun, hz]
  have hle := hf (symmDiff {r} T) hf_ne
  have hT_sub : T ⊆ insert r (symmDiff {r} T) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_symmDiff, Finset.mem_singleton]
    by_cases hxr : x = r
    · exact Or.inl hxr
    · exact Or.inr (Or.inr ⟨hx, hxr⟩)
  calc
    T.card ≤ (insert r (symmDiff {r} T)).card := Finset.card_le_card hT_sub
    _ ≤ (symmDiff {r} T).card + 1 := Finset.card_insert_le _ _
    _ ≤ k + 1 := Nat.add_le_add_right hle 1

private lemma bladeRepr_univ_eq_zero_of_deg_le_two (R : Type*) [CommRing R] :
    (∀ c : R, bladeRepr R 4 (algebraMap R _ c) Finset.univ = 0) ∧
    (∀ a b : Fin 4 → R,
      bladeRepr R 4 (ι (cliffordNegSqForm R 4) a * ι (cliffordNegSqForm R 4) b) Finset.univ = 0) := by
  let e0 : Finset (Fin 4) → R := Pi.single ∅ (1 : R)
  have h0 : ∀ U : Finset (Fin 4), e0 U ≠ 0 → U.card ≤ 0 := by
    intro U hU
    by_cases he : U = ∅
    · subst he; simp
    · exact False.elim (hU (by simp [e0, he]))
  have h1 : ∀ r : Fin 4, ∀ U : Finset (Fin 4),
      leftMulSingle R 4 r e0 U ≠ 0 → U.card ≤ 1 := fun r =>
    leftMulSingle_card_bound h0
  have h2 : ∀ r s : Fin 4, ∀ U : Finset (Fin 4),
      (leftMulSingle R 4 r * leftMulSingle R 4 s) e0 U ≠ 0 →
        U.card ≤ 2 := fun r s =>
    leftMulSingle_card_bound (h1 s)
  constructor
  · intro c
    dsimp only [bladeRepr]
    rw [AlgHom.commutes, Module.algebraMap_end_apply, Pi.smul_apply, smul_eq_mul]
    have hne : (Finset.univ : Finset (Fin 4)) ≠ ∅ := by decide
    simp [hne]
  · intro a b
    have ha : a = ∑ r : Fin 4, a r • Pi.single r (1 : R) := by
      ext i; simp [Finset.sum_apply, Pi.single_apply]
    have hb : b = ∑ s : Fin 4, b s • Pi.single s (1 : R) := by
      ext i; simp [Finset.sum_apply, Pi.single_apply]
    nth_rw 1 [ha]; nth_rw 1 [hb]
    simp_rw [map_sum, map_smul, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm]
    simp only [bladeRepr, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_eq_zero fun r _ => Finset.sum_eq_zero fun s _ => ?_
    have hz : cliffordEndRep R 4 (cGen R 4 r * cGen R 4 s) e0 Finset.univ = 0 := by
      by_contra hne
      rw [map_mul, cliffordEndRep_cGen, cliffordEndRep_cGen] at hne
      have hcard := h2 r s Finset.univ hne
      have h4 : (Finset.univ : Finset (Fin 4)).card = 4 := by decide
      omega
    change a r * (b s * cliffordEndRep R 4 (cGen R 4 r * cGen R 4 s) e0 Finset.univ) = 0
    rw [hz, mul_zero, mul_zero]

private lemma bladeRepr4_swap01 {R : Type*} [CommRing R] (v₀ v₁ v₂ v₃ : Fin 4 → R) :
    bladeRepr R 4 (ι (cliffordNegSqForm R 4) v₀ * ι (cliffordNegSqForm R 4) v₁ *
        ι (cliffordNegSqForm R 4) v₂ * ι (cliffordNegSqForm R 4) v₃) Finset.univ =
      -bladeRepr R 4 (ι (cliffordNegSqForm R 4) v₁ * ι (cliffordNegSqForm R 4) v₀ *
        ι (cliffordNegSqForm R 4) v₂ * ι (cliffordNegSqForm R 4) v₃) Finset.univ := by
  have hdeg := bladeRepr_univ_eq_zero_of_deg_le_two R
  have hpol : ι (cliffordNegSqForm R 4) v₀ * ι (cliffordNegSqForm R 4) v₁ =
      algebraMap R _ (QuadraticMap.polar (cliffordNegSqForm R 4) v₀ v₁) -
        ι (cliffordNegSqForm R 4) v₁ * ι (cliffordNegSqForm R 4) v₀ := ι_mul_ι_comm v₀ v₁
  have hm : ι (cliffordNegSqForm R 4) v₀ * ι (cliffordNegSqForm R 4) v₁ *
        ι (cliffordNegSqForm R 4) v₂ * ι (cliffordNegSqForm R 4) v₃ =
      algebraMap R _ (QuadraticMap.polar (cliffordNegSqForm R 4) v₀ v₁) *
          (ι (cliffordNegSqForm R 4) v₂ * ι (cliffordNegSqForm R 4) v₃) -
        ι (cliffordNegSqForm R 4) v₁ * ι (cliffordNegSqForm R 4) v₀ *
          ι (cliffordNegSqForm R 4) v₂ * ι (cliffordNegSqForm R 4) v₃ := by
    rw [hpol]; noncomm_ring
  have h0 : bladeRepr R 4 (algebraMap R _ (QuadraticMap.polar (cliffordNegSqForm R 4) v₀ v₁) *
      (ι (cliffordNegSqForm R 4) v₂ * ι (cliffordNegSqForm R 4) v₃)) Finset.univ = 0 := by
    rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, bladeRepr, map_smul,
      LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
    change QuadraticMap.polar (cliffordNegSqForm R 4) v₀ v₁ *
      bladeRepr R 4 (ι _ v₂ * ι _ v₃) Finset.univ = 0
    rw [hdeg.2, mul_zero]
  rw [hm]
  simp only [bladeRepr, map_sub, LinearMap.sub_apply, Pi.sub_apply]
  change bladeRepr R 4 (algebraMap R _ _ * _) Finset.univ - _ = -_
  rw [h0, zero_sub]

private lemma bladeRepr4_swap12 {R : Type*} [CommRing R] (v₀ v₁ v₂ v₃ : Fin 4 → R) :
    bladeRepr R 4 (ι (cliffordNegSqForm R 4) v₀ * ι (cliffordNegSqForm R 4) v₁ *
        ι (cliffordNegSqForm R 4) v₂ * ι (cliffordNegSqForm R 4) v₃) Finset.univ =
      -bladeRepr R 4 (ι (cliffordNegSqForm R 4) v₀ * ι (cliffordNegSqForm R 4) v₂ *
        ι (cliffordNegSqForm R 4) v₁ * ι (cliffordNegSqForm R 4) v₃) Finset.univ := by
  have hdeg := bladeRepr_univ_eq_zero_of_deg_le_two R
  have hpol : ι (cliffordNegSqForm R 4) v₁ * ι (cliffordNegSqForm R 4) v₂ =
      algebraMap R _ (QuadraticMap.polar (cliffordNegSqForm R 4) v₁ v₂) -
        ι (cliffordNegSqForm R 4) v₂ * ι (cliffordNegSqForm R 4) v₁ := ι_mul_ι_comm v₁ v₂
  have hm : ι (cliffordNegSqForm R 4) v₀ * ι (cliffordNegSqForm R 4) v₁ *
        ι (cliffordNegSqForm R 4) v₂ * ι (cliffordNegSqForm R 4) v₃ =
      algebraMap R _ (QuadraticMap.polar (cliffordNegSqForm R 4) v₁ v₂) *
          (ι (cliffordNegSqForm R 4) v₀ * ι (cliffordNegSqForm R 4) v₃) -
        ι (cliffordNegSqForm R 4) v₀ * ι (cliffordNegSqForm R 4) v₂ *
          ι (cliffordNegSqForm R 4) v₁ * ι (cliffordNegSqForm R 4) v₃ := by
    calc
      ι (cliffordNegSqForm R 4) v₀ * ι (cliffordNegSqForm R 4) v₁ *
          ι (cliffordNegSqForm R 4) v₂ * ι (cliffordNegSqForm R 4) v₃
          = ι (cliffordNegSqForm R 4) v₀ *
              (ι (cliffordNegSqForm R 4) v₁ * ι (cliffordNegSqForm R 4) v₂) *
              ι (cliffordNegSqForm R 4) v₃ := by noncomm_ring
      _ = ι (cliffordNegSqForm R 4) v₀ *
              (algebraMap R _ (QuadraticMap.polar (cliffordNegSqForm R 4) v₁ v₂) -
                ι (cliffordNegSqForm R 4) v₂ * ι (cliffordNegSqForm R 4) v₁) *
              ι (cliffordNegSqForm R 4) v₃ := by rw [hpol]
      _ = (ι (cliffordNegSqForm R 4) v₀ *
              algebraMap R _ (QuadraticMap.polar (cliffordNegSqForm R 4) v₁ v₂)) *
              ι (cliffordNegSqForm R 4) v₃ -
            ι (cliffordNegSqForm R 4) v₀ * ι (cliffordNegSqForm R 4) v₂ *
              ι (cliffordNegSqForm R 4) v₁ * ι (cliffordNegSqForm R 4) v₃ := by
          noncomm_ring
      _ = algebraMap R _ (QuadraticMap.polar (cliffordNegSqForm R 4) v₁ v₂) *
              (ι (cliffordNegSqForm R 4) v₀ * ι (cliffordNegSqForm R 4) v₃) -
            ι (cliffordNegSqForm R 4) v₀ * ι (cliffordNegSqForm R 4) v₂ *
              ι (cliffordNegSqForm R 4) v₁ * ι (cliffordNegSqForm R 4) v₃ := by
          rw [← Algebra.commutes _ (ι (cliffordNegSqForm R 4) v₀)]
          noncomm_ring
  have h0 : bladeRepr R 4 (algebraMap R _ (QuadraticMap.polar (cliffordNegSqForm R 4) v₁ v₂) *
      (ι (cliffordNegSqForm R 4) v₀ * ι (cliffordNegSqForm R 4) v₃)) Finset.univ = 0 := by
    rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, bladeRepr, map_smul,
      LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
    change QuadraticMap.polar (cliffordNegSqForm R 4) v₁ v₂ *
      bladeRepr R 4 (ι _ v₀ * ι _ v₃) Finset.univ = 0
    rw [hdeg.2, mul_zero]
  rw [hm]
  simp only [bladeRepr, map_sub, LinearMap.sub_apply, Pi.sub_apply]
  change bladeRepr R 4 (algebraMap R _ _ * _) Finset.univ - _ = -_
  rw [h0, zero_sub]

private lemma bladeRepr4_swap23 {R : Type*} [CommRing R] (v₀ v₁ v₂ v₃ : Fin 4 → R) :
    bladeRepr R 4 (ι (cliffordNegSqForm R 4) v₀ * ι (cliffordNegSqForm R 4) v₁ *
        ι (cliffordNegSqForm R 4) v₂ * ι (cliffordNegSqForm R 4) v₃) Finset.univ =
      -bladeRepr R 4 (ι (cliffordNegSqForm R 4) v₀ * ι (cliffordNegSqForm R 4) v₁ *
        ι (cliffordNegSqForm R 4) v₃ * ι (cliffordNegSqForm R 4) v₂) Finset.univ := by
  have hdeg := bladeRepr_univ_eq_zero_of_deg_le_two R
  have hpol : ι (cliffordNegSqForm R 4) v₂ * ι (cliffordNegSqForm R 4) v₃ =
      algebraMap R _ (QuadraticMap.polar (cliffordNegSqForm R 4) v₂ v₃) -
        ι (cliffordNegSqForm R 4) v₃ * ι (cliffordNegSqForm R 4) v₂ := ι_mul_ι_comm v₂ v₃
  have hm : ι (cliffordNegSqForm R 4) v₀ * ι (cliffordNegSqForm R 4) v₁ *
        ι (cliffordNegSqForm R 4) v₂ * ι (cliffordNegSqForm R 4) v₃ =
      algebraMap R _ (QuadraticMap.polar (cliffordNegSqForm R 4) v₂ v₃) *
          (ι (cliffordNegSqForm R 4) v₀ * ι (cliffordNegSqForm R 4) v₁) -
        ι (cliffordNegSqForm R 4) v₀ * ι (cliffordNegSqForm R 4) v₁ *
          ι (cliffordNegSqForm R 4) v₃ * ι (cliffordNegSqForm R 4) v₂ := by
    calc
      ι (cliffordNegSqForm R 4) v₀ * ι (cliffordNegSqForm R 4) v₁ *
          ι (cliffordNegSqForm R 4) v₂ * ι (cliffordNegSqForm R 4) v₃
          = (ι (cliffordNegSqForm R 4) v₀ * ι (cliffordNegSqForm R 4) v₁) *
              (ι (cliffordNegSqForm R 4) v₂ * ι (cliffordNegSqForm R 4) v₃) := by noncomm_ring
      _ = (ι (cliffordNegSqForm R 4) v₀ * ι (cliffordNegSqForm R 4) v₁) *
              (algebraMap R _ (QuadraticMap.polar (cliffordNegSqForm R 4) v₂ v₃) -
                ι (cliffordNegSqForm R 4) v₃ * ι (cliffordNegSqForm R 4) v₂) := by rw [hpol]
      _ = _ := by
          rw [mul_sub, Algebra.commutes]; noncomm_ring
  have h0 : bladeRepr R 4 (algebraMap R _ (QuadraticMap.polar (cliffordNegSqForm R 4) v₂ v₃) *
      (ι (cliffordNegSqForm R 4) v₀ * ι (cliffordNegSqForm R 4) v₁)) Finset.univ = 0 := by
    rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, bladeRepr, map_smul,
      LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
    change QuadraticMap.polar (cliffordNegSqForm R 4) v₂ v₃ *
      bladeRepr R 4 (ι _ v₀ * ι _ v₁) Finset.univ = 0
    rw [hdeg.2, mul_zero]
  rw [hm]
  simp only [bladeRepr, map_sub, LinearMap.sub_apply, Pi.sub_apply]
  change bladeRepr R 4 (algebraMap R _ _ * _) Finset.univ - _ = -_
  rw [h0, zero_sub]

private def cliffordFourDetAlt (R : Type*) [CommRing R] :
    (Fin 4 → R) [⋀^Fin 4]→ₗ[R] R :=
  { toFun := fun M =>
      bladeRepr R 4
        (ι (cliffordNegSqForm R 4) (M 0) * ι (cliffordNegSqForm R 4) (M 1) *
          ι (cliffordNegSqForm R 4) (M 2) * ι (cliffordNegSqForm R 4) (M 3)) Finset.univ
    map_update_add' := fun {inst} M i x y => by
      cases Subsingleton.elim inst (instDecidableEqFin 4)
      have h01 : (0 : Fin 4) ≠ 1 := by simp
      have h02 : (0 : Fin 4) ≠ 2 := by simp [Fin.ext_iff]
      have h03 : (0 : Fin 4) ≠ 3 := by simp [Fin.ext_iff]
      have h12 : (1 : Fin 4) ≠ 2 := by simp [Fin.ext_iff]
      have h13 : (1 : Fin 4) ≠ 3 := by simp [Fin.ext_iff]
      have h23 : (2 : Fin 4) ≠ 3 := by simp [Fin.ext_iff]
      rcases i with ⟨_ | _ | _ | _ | i, hi⟩
      · have hi0 : (⟨0, hi⟩ : Fin 4) = 0 := Fin.ext rfl; rw [hi0]
        rw [Function.update_self, Function.update_of_ne h01.symm, Function.update_of_ne h02.symm,
          Function.update_of_ne h03.symm, map_add, add_mul, add_mul, add_mul, bladeRepr, map_add,
          LinearMap.add_apply, Pi.add_apply]
        rfl
      · have hi1 : (⟨1, hi⟩ : Fin 4) = 1 := Fin.ext rfl; rw [hi1]
        rw [Function.update_of_ne h01, Function.update_self, Function.update_of_ne h12.symm,
          Function.update_of_ne h13.symm, map_add, mul_add, add_mul, add_mul, bladeRepr, map_add,
          LinearMap.add_apply, Pi.add_apply]
        rfl
      · have hi2 : (⟨2, hi⟩ : Fin 4) = 2 := Fin.ext rfl; rw [hi2]
        rw [Function.update_of_ne h02, Function.update_of_ne h12, Function.update_self,
          Function.update_of_ne h23.symm, map_add, mul_add, add_mul, bladeRepr, map_add,
          LinearMap.add_apply, Pi.add_apply]
        rfl
      · have hi3 : (⟨3, hi⟩ : Fin 4) = 3 := Fin.ext rfl; rw [hi3]
        rw [Function.update_of_ne h03, Function.update_of_ne h13, Function.update_of_ne h23,
          Function.update_self, map_add, mul_add, bladeRepr, map_add, LinearMap.add_apply,
          Pi.add_apply]
        rfl
      · omega
    map_update_smul' := fun {inst} M i c x => by
      cases Subsingleton.elim inst (instDecidableEqFin 4)
      have h01 : (0 : Fin 4) ≠ 1 := by simp
      have h02 : (0 : Fin 4) ≠ 2 := by simp [Fin.ext_iff]
      have h03 : (0 : Fin 4) ≠ 3 := by simp [Fin.ext_iff]
      have h12 : (1 : Fin 4) ≠ 2 := by simp [Fin.ext_iff]
      have h13 : (1 : Fin 4) ≠ 3 := by simp [Fin.ext_iff]
      have h23 : (2 : Fin 4) ≠ 3 := by simp [Fin.ext_iff]
      rcases i with ⟨_ | _ | _ | _ | i, hi⟩
      · have hi0 : (⟨0, hi⟩ : Fin 4) = 0 := Fin.ext rfl; rw [hi0]
        rw [Function.update_self, Function.update_of_ne h01.symm, Function.update_of_ne h02.symm,
          Function.update_of_ne h03.symm, map_smul, smul_mul_assoc, smul_mul_assoc,
          smul_mul_assoc, bladeRepr, map_smul, LinearMap.smul_apply, Pi.smul_apply]
        rfl
      · have hi1 : (⟨1, hi⟩ : Fin 4) = 1 := Fin.ext rfl; rw [hi1]
        rw [Function.update_of_ne h01, Function.update_self, Function.update_of_ne h12.symm,
          Function.update_of_ne h13.symm, map_smul, mul_smul_comm, smul_mul_assoc,
          smul_mul_assoc, bladeRepr, map_smul, LinearMap.smul_apply, Pi.smul_apply]
        rfl
      · have hi2 : (⟨2, hi⟩ : Fin 4) = 2 := Fin.ext rfl; rw [hi2]
        rw [Function.update_of_ne h02, Function.update_of_ne h12, Function.update_self,
          Function.update_of_ne h23.symm, map_smul, mul_smul_comm, smul_mul_assoc, bladeRepr,
          map_smul, LinearMap.smul_apply, Pi.smul_apply]
        rfl
      · have hi3 : (⟨3, hi⟩ : Fin 4) = 3 := Fin.ext rfl; rw [hi3]
        rw [Function.update_of_ne h03, Function.update_of_ne h13, Function.update_of_ne h23,
          Function.update_self, map_smul, mul_smul_comm, bladeRepr, map_smul,
          LinearMap.smul_apply, Pi.smul_apply]
        rfl
      · omega
    map_eq_zero_of_eq' := fun M {i j} hij hne => by
      have hdeg := bladeRepr_univ_eq_zero_of_deg_le_two R
      have hlin_deg02 : ∀ (c : R) (u v : Fin 4 → R),
          bladeRepr R 4 (algebraMap R _ c *
            (ι (cliffordNegSqForm R 4) u * ι (cliffordNegSqForm R 4) v)) Finset.univ = 0 := by
        intro c u v
        rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, bladeRepr, map_smul,
          LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
        change c * bladeRepr R 4 (ι _ u * ι _ v) Finset.univ = 0
        rw [hdeg.2, mul_zero]
      have hadj0 : ∀ u v₂ v₃ : Fin 4 → R,
          bladeRepr R 4 (ι (cliffordNegSqForm R 4) u * ι (cliffordNegSqForm R 4) u *
            ι (cliffordNegSqForm R 4) v₂ * ι (cliffordNegSqForm R 4) v₃) Finset.univ = 0 := by
        intro u v₂ v₃
        rw [ι_sq_scalar, mul_assoc]
        exact hlin_deg02 _ v₂ v₃
      have hadj1 : ∀ v₀ u v₃ : Fin 4 → R,
          bladeRepr R 4 (ι (cliffordNegSqForm R 4) v₀ * ι (cliffordNegSqForm R 4) u *
            ι (cliffordNegSqForm R 4) u * ι (cliffordNegSqForm R 4) v₃) Finset.univ = 0 := by
        intro v₀ u v₃
        rw [bladeRepr4_swap01, bladeRepr4_swap12, hadj0, neg_zero, neg_zero]
      have hadj2 : ∀ v₀ v₁ u : Fin 4 → R,
          bladeRepr R 4 (ι (cliffordNegSqForm R 4) v₀ * ι (cliffordNegSqForm R 4) v₁ *
            ι (cliffordNegSqForm R 4) u * ι (cliffordNegSqForm R 4) u) Finset.univ = 0 := by
        intro v₀ v₁ u
        rw [bladeRepr4_swap12, bladeRepr4_swap23, hadj1, neg_zero, neg_zero]
      fin_cases i <;> fin_cases j <;> simp at hne
      · have heq : M 0 = M 1 := hij; rw [heq]; exact hadj0 (M 1) (M 2) (M 3)
      · have heq : M 0 = M 2 := hij; rw [bladeRepr4_swap12, heq, hadj0, neg_zero]
      · have heq : M 0 = M 3 := hij
        rw [bladeRepr4_swap23, bladeRepr4_swap12, heq, hadj0, neg_zero, neg_zero]
      · have heq : M 1 = M 0 := hij; rw [heq]; exact hadj0 (M 0) (M 2) (M 3)
      · have heq : M 1 = M 2 := hij; rw [heq]; exact hadj1 (M 0) (M 2) (M 3)
      · have heq : M 1 = M 3 := hij; rw [bladeRepr4_swap23, heq, hadj1, neg_zero]
      · have heq : M 2 = M 0 := hij; rw [bladeRepr4_swap12, heq, hadj0, neg_zero]
      · have heq : M 2 = M 1 := hij; rw [heq]; exact hadj1 (M 0) (M 1) (M 3)
      · have heq : M 2 = M 3 := hij; rw [heq]; exact hadj2 (M 0) (M 1) (M 3)
      · have heq : M 3 = M 0 := hij
        rw [bladeRepr4_swap23, bladeRepr4_swap12, heq, hadj0, neg_zero, neg_zero]
      · have heq : M 3 = M 1 := hij; rw [bladeRepr4_swap23, heq, hadj1, neg_zero]
      · have heq : M 3 = M 2 := hij; rw [heq]; exact hadj2 (M 0) (M 1) (M 2) }

/-- Clifford's four-point determinant theorem (`p. 353`):
the top `ω₄`-coefficient of the Clifford product `α β γ δ` of four points in `ℝ⁴` (or `R⁴`)
equals `det M` over any commutative ring `R`. -/
theorem clifford_fourPoint_det (R : Type*) [CommRing R] (M : Matrix (Fin 4) (Fin 4) R) :
    bladeRepr R 4
        (ι (cliffordNegSqForm R 4) (M 0) * ι (cliffordNegSqForm R 4) (M 1) *
          ι (cliffordNegSqForm R 4) (M 2) * ι (cliffordNegSqForm R 4) (M 3)) Finset.univ =
      M.det := by
  have heq := AlternatingMap.eq_smul_basis_det (Pi.basisFun R (Fin 4)) (cliffordFourDetAlt R)
  have hval : cliffordFourDetAlt R (Pi.basisFun R (Fin 4)) = 1 := by
    change bladeRepr R 4
      (ι (cliffordNegSqForm R 4) ((Pi.basisFun R (Fin 4)) 0) *
        ι (cliffordNegSqForm R 4) ((Pi.basisFun R (Fin 4)) 1) *
        ι (cliffordNegSqForm R 4) ((Pi.basisFun R (Fin 4)) 2) *
        ι (cliffordNegSqForm R 4) ((Pi.basisFun R (Fin 4)) 3)) Finset.univ = 1
    simp only [Pi.basisFun_apply]
    change bladeRepr R 4
      (cGen R 4 0 * cGen R 4 1 * cGen R 4 2 * cGen R 4 3) Finset.univ = 1
    rw [← ω₄_eq_mul R, ω₄, bladeRepr_cBlade]
    simp
  have hfun := congrArg (fun f => f M) heq
  rw [hval, one_smul, Pi.basisFun_det] at hfun
  exact hfun

/-- Clifford's biquaternion 6-bivector `D + ω₄ M` (`p. 354`, line-complex / motor bivector). -/
def biquatBivector (R : Type*) [CommRing R] (d m : Fin 3 → R) :
    CliffordAlgebra (cliffordNegSqForm R 4) :=
  (d 0 • q4I R + d 1 • q4J R + d 2 • q4K R) +
    ω₄ R * (m 0 • q4I R + m 1 • q4J R + m 2 • q4K R)

private lemma pure_bivector4_sq_and_anti (R : Type*) [CommRing R] (d m : Fin 3 → R) :
    (d 0 • q4I R + d 1 • q4J R + d 2 • q4K R) *
        (d 0 • q4I R + d 1 • q4J R + d 2 • q4K R) =
      algebraMap R _ (-(d ⬝ᵥ d)) ∧
    (m 0 • q4I R + m 1 • q4J R + m 2 • q4K R) *
        (m 0 • q4I R + m 1 • q4J R + m 2 • q4K R) =
      algebraMap R _ (-(m ⬝ᵥ m)) ∧
    (d 0 • q4I R + d 1 • q4J R + d 2 • q4K R) *
        (m 0 • q4I R + m 1 • q4J R + m 2 • q4K R) +
      (m 0 • q4I R + m 1 • q4J R + m 2 • q4K R) *
        (d 0 • q4I R + d 1 • q4J R + d 2 • q4K R) =
      algebraMap R _ (-((2 : R) * (d ⬝ᵥ m))) := by
  have hlaws := clifford_cl04_quaternion_relations R
  rcases hlaws with ⟨hi2, hj2, hk2, hjk, hki, hij, _⟩
  have hkj : q4K R * q4J R = -q4I R := by
    calc q4K R * q4J R = (q4I R * q4J R) * q4J R := by rw [hij]
    _ = q4I R * (q4J R * q4J R) := mul_assoc _ _ _
    _ = -q4I R := by rw [hj2]; noncomm_ring
  have hik : q4I R * q4K R = -q4J R := by
    calc q4I R * q4K R = (q4J R * q4K R) * q4K R := by rw [hjk]
    _ = q4J R * (q4K R * q4K R) := mul_assoc _ _ _
    _ = -q4J R := by rw [hk2]; noncomm_ring
  have hji : q4J R * q4I R = -q4K R := by
    calc q4J R * q4I R = (q4K R * q4I R) * q4I R := by rw [hki]
    _ = q4K R * (q4I R * q4I R) := mul_assoc _ _ _
    _ = -q4K R := by rw [hi2]; noncomm_ring
  have hbilinear : ∀ a b : Fin 3 → R,
      (a 0 • q4I R + a 1 • q4J R + a 2 • q4K R) *
          (b 0 • q4I R + b 1 • q4J R + b 2 • q4K R) =
        algebraMap R _ (-(a ⬝ᵥ b)) +
          (a 1 * b 2 - a 2 * b 1) • q4I R +
          (a 2 * b 0 - a 0 * b 2) • q4J R +
          (a 0 * b 1 - a 1 * b 0) • q4K R := by
    intro a b
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
      hi2, hj2, hk2, hjk, hkj, hki, hik, hij, hji, smul_neg, dotProduct, Fin.sum_univ_three,
      Algebra.algebraMap_eq_smul_one, neg_add_rev, neg_smul, sub_eq_add_neg, add_smul]
    module
  refine ⟨?_, ?_, ?_⟩
  · have hd := hbilinear d d
    rw [mul_comm (d 2) (d 1), mul_comm (d 0) (d 2), mul_comm (d 1) (d 0),
      sub_self, sub_self, sub_self] at hd
    simpa using hd
  · have hm := hbilinear m m
    rw [mul_comm (m 2) (m 1), mul_comm (m 0) (m 2), mul_comm (m 1) (m 0),
      sub_self, sub_self, sub_self] at hm
    simpa using hm
  · rw [hbilinear d m, hbilinear m d, Algebra.algebraMap_eq_smul_one,
      Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, dotProduct_comm m d]
    simp only [sub_eq_add_neg, add_smul, neg_smul]
    module

/-- Biquaternion 6-bivector square law (`p. 354`):
`(D + ω₄ M)² = -(‖d‖² + ‖m‖²) - 2 (d ⬝ᵥ m) ω₄`. -/
theorem biquatBivector_sq (R : Type*) [CommRing R] (d m : Fin 3 → R) :
    biquatBivector R d m * biquatBivector R d m =
      algebraMap R _ (-(d ⬝ᵥ d + m ⬝ᵥ m)) - ((2 : R) * (d ⬝ᵥ m)) • ω₄ R := by
  have hpol := (ω₄_polar_points_scalar_versors R).2
  rcases hpol with ⟨hci, hcj, hck⟩
  have hcomm_comb : ∀ a : Fin 3 → R,
      ω₄ R * (a 0 • q4I R + a 1 • q4J R + a 2 • q4K R) =
        (a 0 • q4I R + a 1 • q4J R + a 2 • q4K R) * ω₄ R := by
    intro a
    simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, hci, hcj, hck]
  have hsq := pure_bivector4_sq_and_anti R d m
  rcases hsq with ⟨hDD, hMM, hanti⟩
  let D := d 0 • q4I R + d 1 • q4J R + d 2 • q4K R
  let M := m 0 • q4I R + m 1 • q4J R + m 2 • q4K R
  have hωM_sq : (ω₄ R * M) * (ω₄ R * M) = M * M := by
    calc
      (ω₄ R * M) * (ω₄ R * M) = ω₄ R * (M * ω₄ R) * M := by noncomm_ring
      _ = ω₄ R * (ω₄ R * M) * M := by rw [hcomm_comb m]
      _ = (ω₄ R * ω₄ R) * (M * M) := by noncomm_ring
      _ = M * M := by rw [ω₄_sq R, one_mul]
  have hcross : D * (ω₄ R * M) + (ω₄ R * M) * D = ω₄ R * (D * M + M * D) := by
    calc
      D * (ω₄ R * M) + (ω₄ R * M) * D = (D * ω₄ R) * M + ω₄ R * (M * D) := by noncomm_ring
      _ = (ω₄ R * D) * M + ω₄ R * (M * D) := by rw [← hcomm_comb d]
      _ = ω₄ R * (D * M + M * D) := by noncomm_ring
  calc
    biquatBivector R d m * biquatBivector R d m
        = D * D + (ω₄ R * M) * (ω₄ R * M) + (D * (ω₄ R * M) + (ω₄ R * M) * D) := by
          change (D + ω₄ R * M) * (D + ω₄ R * M) = _; noncomm_ring
    _ = algebraMap R _ (-(d ⬝ᵥ d)) + algebraMap R _ (-(m ⬝ᵥ m)) +
          ω₄ R * algebraMap R _ (-((2 : R) * (d ⬝ᵥ m))) := by
          rw [hDD, hωM_sq, hMM, hcross, hanti]
    _ = algebraMap R _ (-(d ⬝ᵥ d + m ⬝ᵥ m)) - ((2 : R) * (d ⬝ᵥ m)) • ω₄ R := by
          rw [← map_add, ← neg_add, ← Algebra.commutes, ← Algebra.smul_def, neg_smul,
            ← sub_eq_add_neg]

/-- **Bridge VIb (`Plücker 1868/1869 kleinQ` ↔ `Clifford 1878 Biquaternion Bivector Square`)**:
over `ℝ`, the `ω₄`-pseudoscalar part of `(D + ω₄ M)²` is `-2 * (directionMomentEquiv.symm (d, m)).kleinQ`,
hence vanishes if and only if the biquaternion bivector represents a Plücker Klein ray (`kleinQ = 0`). -/
theorem biquatBivector_sq_plucker_kleinQ (d m : Vec3) :
    biquatBivector ℝ d m * biquatBivector ℝ d m =
      algebraMap ℝ _ (-(d ⬝ᵥ d + m ⬝ᵥ m)) -
        (2 * (directionMomentEquiv.symm (d, m)).kleinQ) • ω₄ ℝ := by
  rw [biquatBivector_sq, kleinQ_directionMoment d m]

/-- Gauss 2-unit complex imaginary generator `i = ι₀ ι₁` in `Cl(0, 2)` (`p. 354`). -/
def gaussImag (R : Type*) [CommRing R] : CliffordAlgebra (cliffordNegSqForm R 2) :=
  cGen R 2 0 * cGen R 2 1

theorem gaussImag_sq (R : Type*) [CommRing R] : gaussImag R * gaussImag R = -1 := by
  have h10 : cGen R 2 1 * cGen R 2 0 = -(cGen R 2 0 * cGen R 2 1) := cGen_anticomm (by decide)
  calc
    gaussImag R * gaussImag R = cGen R 2 0 * (cGen R 2 1 * cGen R 2 0) * cGen R 2 1 := by
      simp [gaussImag, mul_assoc]
    _ = cGen R 2 0 * -(cGen R 2 0 * cGen R 2 1) * cGen R 2 1 := by rw [h10]
    _ = -((cGen R 2 0 * cGen R 2 0) * (cGen R 2 1 * cGen R 2 1)) := by noncomm_ring
    _ = -1 := by rw [cGen_sq, cGen_sq]; noncomm_ring

private lemma gaussBilin_map_add (u v w : Fin 2 → ℝ) :
    -((u ⬝ᵥ (v + w) : ℝ) : ℂ) + (u 0 * (v + w) 1 - u 1 * (v + w) 0 : ℝ) • Complex.I =
      (-((u ⬝ᵥ v : ℝ) : ℂ) + (u 0 * v 1 - u 1 * v 0 : ℝ) • Complex.I) +
        (-((u ⬝ᵥ w : ℝ) : ℂ) + (u 0 * w 1 - u 1 * w 0 : ℝ) • Complex.I) := by
  simp only [dotProduct_add, Pi.add_apply, Complex.ofReal_add, Complex.real_smul]
  push_cast
  ring

private lemma gaussBilin_map_smul (r : ℝ) (u v : Fin 2 → ℝ) :
    -((u ⬝ᵥ (r • v) : ℝ) : ℂ) + (u 0 * (r • v) 1 - u 1 * (r • v) 0 : ℝ) • Complex.I =
      r • (-((u ⬝ᵥ v : ℝ) : ℂ) + (u 0 * v 1 - u 1 * v 0 : ℝ) • Complex.I) := by
  simp only [dotProduct_smul, Pi.smul_apply, smul_eq_mul, Complex.real_smul]
  push_cast
  ring

/-- Clifford's 2-unit even algebra map `Cl⁰(0, 2) →ₐ[ℝ] ℂ` (`p. 354`). -/
def gaussEvenToComplex : CliffordAlgebra.even (cliffordNegSqForm ℝ 2) →ₐ[ℝ] ℂ :=
  CliffordAlgebra.even.lift (cliffordNegSqForm ℝ 2)
    ⟨{ toFun := fun u =>
        { toFun := fun v => -((u ⬝ᵥ v : ℝ) : ℂ) + (u 0 * v 1 - u 1 * v 0 : ℝ) • Complex.I
          map_add' := fun v w => gaussBilin_map_add u v w
          map_smul' := fun r v => gaussBilin_map_smul r u v }
       map_add' := fun u w => by
        refine LinearMap.ext fun v => ?_
        simp only [add_dotProduct, Pi.add_apply, LinearMap.add_apply, LinearMap.coe_mk,
          AddHom.coe_mk, Complex.real_smul]
        push_cast
        ring
       map_smul' := fun r u => by
        refine LinearMap.ext fun v => ?_
        simp only [smul_dotProduct, Pi.smul_apply, LinearMap.smul_apply, LinearMap.coe_mk,
          AddHom.coe_mk, smul_eq_mul, RingHom.id_apply, Complex.real_smul]
        push_cast
        ring },
     fun u => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, cliffordNegSqForm_apply, Fin.sum_univ_two,
        dotProduct, Algebra.algebraMap_eq_smul_one, Complex.real_smul, mul_one]
      apply Complex.ext
      · simp
      · simp; ring,
     fun m₁ m₂ m₃ => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, cliffordNegSqForm_apply, Fin.sum_univ_two,
        dotProduct, Complex.real_smul]
      apply Complex.ext
      · simp; ring
      · simp; ring⟩

/-- Gauss 2-unit even algebra equivalence `Cl⁰(0, 2) ≃ₐ[ℝ] ℂ` (`p. 354`). -/
def gaussEvenAlgEquivComplex : CliffordAlgebra.even (cliffordNegSqForm ℝ 2) ≃ₐ[ℝ] ℂ :=
  let gI : CliffordAlgebra.even (cliffordNegSqForm ℝ 2) :=
    ⟨gaussImag ℝ, by
      change cGen ℝ 2 0 * cGen ℝ 2 1 ∈ Subalgebra.toSubmodule (CliffordAlgebra.even (cliffordNegSqForm ℝ 2))
      rw [CliffordAlgebra.even_toSubmodule]
      exact CliffordAlgebra.ι_mul_ι_mem_evenOdd_zero _ _ _⟩
  let back : ℂ →ₐ[ℝ] CliffordAlgebra.even (cliffordNegSqForm ℝ 2) :=
    Complex.lift ⟨gI, Subtype.ext (gaussImag_sq ℝ)⟩
  AlgEquiv.ofAlgHom gaussEvenToComplex back
    (by
      ext1
      change gaussEvenToComplex (back Complex.I) = Complex.I
      have hb : back Complex.I = gI :=
        Complex.liftAux_apply_I gI (Subtype.ext (gaussImag_sq ℝ))
      rw [hb]
      have hbilin : gI = (CliffordAlgebra.even.ι (cliffordNegSqForm ℝ 2)).bilin
          (Pi.single 0 1) (Pi.single 1 1) := by
        ext1; rfl
      rw [hbilin, gaussEvenToComplex, even.lift_ι]
      simp [dotProduct, Fin.sum_univ_two, Complex.real_smul])
    (by
      refine CliffordAlgebra.even.algHom_ext _ (EvenHom.ext (LinearMap.ext fun u =>
        LinearMap.ext fun v => Subtype.ext ?_))
      have hback : ∀ z : ℂ, (back z : CliffordAlgebra (cliffordNegSqForm ℝ 2)) =
          z.re • 1 + z.im • gaussImag ℝ := by
        intro z
        change ((Complex.liftAux gI (Subtype.ext (gaussImag_sq ℝ)) z : _) :
            CliffordAlgebra (cliffordNegSqForm ℝ 2)) = _
        rw [Complex.liftAux_apply, Subalgebra.coe_add, Subalgebra.coe_smul]
        change algebraMap ℝ (CliffordAlgebra (cliffordNegSqForm ℝ 2)) z.re + z.im • gaussImag ℝ = _
        rw [Algebra.algebraMap_eq_smul_one]
      change (back (gaussEvenToComplex
          ((CliffordAlgebra.even.ι (cliffordNegSqForm ℝ 2)).bilin u v)) :
          CliffordAlgebra (cliffordNegSqForm ℝ 2)) =
        ((CliffordAlgebra.even.ι (cliffordNegSqForm ℝ 2)).bilin u v :
          CliffordAlgebra (cliffordNegSqForm ℝ 2))
      rw [gaussEvenToComplex, even.lift_ι]
      dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
      rw [hback]
      have hu : u = u 0 • Pi.single 0 (1 : ℝ) + u 1 • Pi.single 1 (1 : ℝ) := by
        ext i; fin_cases i <;> simp
      have hv : v = v 0 • Pi.single 0 (1 : ℝ) + v 1 • Pi.single 1 (1 : ℝ) := by
        ext i; fin_cases i <;> simp
      have hre : ((-((u ⬝ᵥ v : ℝ) : ℂ) + (u 0 * v 1 - u 1 * v 0 : ℝ) • Complex.I)).re = -(u ⬝ᵥ v) := by
        simp [Complex.real_smul]
      have him : ((-((u ⬝ᵥ v : ℝ) : ℂ) + (u 0 * v 1 - u 1 * v 0 : ℝ) • Complex.I)).im =
          u 0 * v 1 - u 1 * v 0 := by
        simp [Complex.real_smul]
      rw [hre, him]
      change -(u ⬝ᵥ v) • (1 : CliffordAlgebra (cliffordNegSqForm ℝ 2)) +
          (u 0 * v 1 - u 1 * v 0) • gaussImag ℝ =
        ι (cliffordNegSqForm ℝ 2) u * ι (cliffordNegSqForm ℝ 2) v
      conv_rhs =>
        rw [hu, hv]
        simp only [map_add, map_smul]
      have h10 : cGen ℝ 2 1 * cGen ℝ 2 0 = -(cGen ℝ 2 0 * cGen ℝ 2 1) := cGen_anticomm (by decide)
      have h00 : cGen ℝ 2 0 * cGen ℝ 2 0 = -1 := cGen_sq ℝ 2 0
      have h11 : cGen ℝ 2 1 * cGen ℝ 2 1 = -1 := cGen_sq ℝ 2 1
      change _ = (u 0 • cGen ℝ 2 0 + u 1 • cGen ℝ 2 1) * (v 0 • cGen ℝ 2 0 + v 1 • cGen ℝ 2 1)
      simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, h00, h11, h10,
        gaussImag, dotProduct, Fin.sum_univ_two, smul_neg, neg_smul, sub_eq_add_neg, add_smul]
      module)

end Sec2BiquaternionsPolarAndBridgeVIbVIIb

end InfoGeometry.Clifford.CliffordExtensiveRotorsAndBiquaternions
