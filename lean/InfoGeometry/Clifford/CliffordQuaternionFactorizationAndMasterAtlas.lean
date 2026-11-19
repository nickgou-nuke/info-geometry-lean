/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.CliffordExtensiveRotorsAndBiquaternions
import InfoGeometry.Projective.GrassmannMeanMotionAndTidalHarmonics
import InfoGeometry.Canonical.GrassmannProductQuotientAndMasterAtlas
import InfoGeometry.Projective.PluckerKummerQuarticAndMasterAtlas
import Mathlib.Algebra.QuaternionBasis
import Mathlib.Tactic

/-!
# Clifford (1878) Part II: `(2m+1)`-Way Quaternion Factorization, Even Doubling & Pentad Master Atlas

This module formalizes Archetypes `CL₄`, `CL₅`, `CL₆`, countermodel `C-CL1`, **Bridge VIII**,
and the **1862–1878 Five-Work Pentad Synthesis** uniting Grassmann (1862), Plücker (1868/1869),
Klein (1872), Grassmann (1877), and Clifford (1878):

1. **`CL₄` (`pp. 355–358`) — Odd `(2m+1)`-Way Algebras & Commuting Quaternion Factorization**:
   - Defines `ωOdd R m = ι₀ ⋯ ι₂ₘ` and `kUnit R m r = ωOdd R m * cGen R (2m+1) r`, proving
     centrality of `ωOdd`, `kUnit` parity, anticommutation, `kUnit² = (-1)^m`, and the volume
     identity `k₀ k₁ ⋯ k₂ₘ = (-1)^(m+1)` (`p. 356`).
   - **`[countermodel_found]` (`C-CL1`, `m = 2`)**: Explicit zero divisors `(1 + k₀)(1 - k₀) = 0`
     in the 5-way Clifford algebra `Cl⁰(0, 5)` over `ℝ`, separating split quaternion factors
     (`k_r² = +1`) from division quaternions.
   - Constructs Clifford's explicit alternating `p`-sets and `q`-sets (`p. 357`) for ALL `m ≥ 1`,
     proving:
     * Each factor `j : Fin m` forms a `QuaternionAlgebra.Basis` (`cFactor = (-1)^(|K_1|)` signs);
     * Distinct factors pairwise commute (`Commute (factorElem i a) (factorElem j b)` for `i ≠ j`);
     * Exact signed even-blade formula and **bijective `4^m = 2^(2m)` enumeration** of all even
       basis blades `evenSupportOfTuple m` (`p. 358`).
2. **`CL₅` (`p. 358`) & Bridge VIII — Even `2m`-Way Double Algebra `(1, ω₂ₘ)` & Chiral Idempotents**:
   - Proves `ωEven R m` (`m ≥ 1`) squares to `(-1)^m`, commutes with all even blades while
     anticommuting with all generators, and induces the explicit `2^(2m-1) = 2^(2m-2) + 2^(2m-2)`
     even-blade doubling bijection.
   - **Bridge VIII**: Instantiates Mathlib's `CliffordAlgebra.equivEven` isomorphism and proves the
     chiral biquaternion Peirce idempotent decomposition `biquatIdempPlus, biquatIdempMinus`.
3. **`CL₆` — 12-Node Grassmann–Clifford Causal Poset & Five-Work Pentad Synthesis**:
   - Constructs the downward-closed bitmask poset `PartialOrder GrassmannClifford1877_1878Archetype`,
     branching witnesses, `grassmann_clifford_1877_1878_master_synthesis`, and
     `grassmann1862_plucker1868_klein1872_grassmann1877_clifford1878_pentad_synthesis`.
-/

noncomputable section

namespace InfoGeometry.Clifford.CliffordQuaternionFactorizationAndMasterAtlas

open Matrix CliffordAlgebra QuadraticForm
open scoped Matrix
open InfoGeometry.Projective.KleinQuadric
open InfoGeometry.Projective.PluckerMatrixAction
open InfoGeometry.Projective.PluckerAffineScrew
open InfoGeometry.Projective.PluckerRayAxisAndDyname
open InfoGeometry.Projective.PluckerQuadraticComplexAndSurfaces
open InfoGeometry.Projective.GrassmannPluckerMeetAndCircleSpace
open InfoGeometry.Clifford.CliffordExtensiveRotorsAndBiquaternions
open InfoGeometry.Projective.GrassmannMechanicsBarycenterAndPotentials
open InfoGeometry.Projective.GrassmannMeanMotionAndTidalHarmonics
open InfoGeometry.Canonical.GrassmannProductQuotientAndMasterAtlas
open InfoGeometry.Projective.PluckerKummerQuarticAndMasterAtlas
open InfoGeometry.Erlangen.ErlangenProgramCurvatureBinaryAndMasterAtlas

section OddWayGenerators

/-- Pseudoscalar `ω = ι₀ ι₁ ⋯ ι_{2m}` in Clifford's odd-dimensional algebra `Cl(0, 2m+1)`
(`p. 356`). -/
def ωOdd (R : Type*) [CommRing R] (m : ℕ) :
    CliffordAlgebra (cliffordNegSqForm R (2 * m + 1)) :=
  cBlade R (2 * m + 1) Finset.univ

/-- Compound generators `k_r = ω ι_r` of order `2m` (`r : Fin (2m + 1)`) (`p. 356`). -/
def kUnit (R : Type*) [CommRing R] (m : ℕ) (r : Fin (2 * m + 1)) :
    CliffordAlgebra (cliffordNegSqForm R (2 * m + 1)) :=
  ωOdd R m * cGen R (2 * m + 1) r

theorem ωOdd_comm_cGen (R : Type*) [CommRing R] (m : ℕ) (r : Fin (2 * m + 1)) :
    cGen R (2 * m + 1) r * ωOdd R m = ωOdd R m * cGen R (2 * m + 1) r := by
  have h := cGen_mul_cBlade R (2 * m + 1) r Finset.univ
  simp only [Finset.card_fin, Finset.mem_univ, ↓reduceIte] at h
  have hpow : (-1 : R) ^ (2 * m + 1 + 1) = 1 := by
    have : 2 * m + 1 + 1 = 2 * (m + 1) := by ring
    rw [this, pow_mul]
    simp
  simpa [ωOdd, hpow] using h

theorem ωOdd_sq (R : Type*) [CommRing R] (m : ℕ) :
    ωOdd R m * ωOdd R m = ((-1 : R) ^ (m + 1)) • 1 := by
  have h := cBlade_sq R (2 * m + 1) Finset.univ
  have hcard : (Finset.univ : Finset (Fin (2 * m + 1))).card = 2 * m + 1 := by simp
  rw [hcard] at h
  have hmod : (2 * m + 1) * (2 * m + 1 + 1) / 2 ≡ m + 1 [MOD 2] := by
    have heq : (2 * m + 1) * (2 * m + 1 + 1) / 2 = (2 * m + 1) * (m + 1) := by
      have hnum : (2 * m + 1) * (2 * m + 1 + 1) = 2 * ((2 * m + 1) * (m + 1)) := by ring
      rw [hnum, Nat.mul_div_right _ (by decide)]
    rw [heq, Nat.ModEq]
    have hmul : (2 * m + 1) * (m + 1) = 2 * (m * (m + 1)) + (m + 1) := by ring
    rw [hmul, Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_mod]
  simpa [ωOdd, neg_one_pow_eq_of_modEq hmod] using h

theorem kUnit_sq (R : Type*) [CommRing R] (m : ℕ) (r : Fin (2 * m + 1)) :
    kUnit R m r * kUnit R m r = ((-1 : R) ^ m) • 1 := by
  calc
    kUnit R m r * kUnit R m r
        = (ωOdd R m * cGen R (2 * m + 1) r) * (cGen R (2 * m + 1) r * ωOdd R m) := by
          simp only [kUnit, ωOdd_comm_cGen]
    _ = ωOdd R m * (cGen R (2 * m + 1) r * cGen R (2 * m + 1) r) * ωOdd R m := by noncomm_ring
    _ = -(ωOdd R m * ωOdd R m) := by rw [cGen_sq]; noncomm_ring
    _ = -(((-1 : R) ^ (m + 1)) • (1 : CliffordAlgebra _)) := by rw [ωOdd_sq]
    _ = ((-1 : R) ^ m) • 1 := by rw [pow_succ, mul_neg_one, neg_smul, neg_neg]

theorem kUnit_anticomm (R : Type*) [CommRing R] (m : ℕ) {r s : Fin (2 * m + 1)} (hrs : r ≠ s) :
    kUnit R m r * kUnit R m s = -(kUnit R m s * kUnit R m r) := by
  calc
    kUnit R m r * kUnit R m s
        = ωOdd R m * (cGen R (2 * m + 1) r * ωOdd R m) * cGen R (2 * m + 1) s := by
          simp only [kUnit, mul_assoc]
    _ = (ωOdd R m * ωOdd R m) * (cGen R (2 * m + 1) r * cGen R (2 * m + 1) s) := by
          rw [ωOdd_comm_cGen]; noncomm_ring
    _ = -((ωOdd R m * ωOdd R m) * (cGen R (2 * m + 1) s * cGen R (2 * m + 1) r)) := by
          rw [cGen_anticomm hrs]; noncomm_ring
    _ = -(kUnit R m s * kUnit R m r) := by
          calc
            -((ωOdd R m * ωOdd R m) * (cGen R (2 * m + 1) s * cGen R (2 * m + 1) r))
                = -(ωOdd R m * (ωOdd R m * cGen R (2 * m + 1) s) * cGen R (2 * m + 1) r) := by
                  noncomm_ring
            _ = -(ωOdd R m * (cGen R (2 * m + 1) s * ωOdd R m) * cGen R (2 * m + 1) r) := by
                  rw [ωOdd_comm_cGen]
            _ = -(kUnit R m s * kUnit R m r) := by simp only [kUnit]; noncomm_ring

private lemma listProd_even_mem_even (R : Type*) [CommRing R] {n : ℕ} :
    ∀ L : List (Fin n), Even L.length →
      ((L.map (cGen R n)).prod) ∈ CliffordAlgebra.even (cliffordNegSqForm R n)
  | [], _ => by simp only [List.map_nil, List.prod_nil]; exact Subalgebra.one_mem _
  | [_], h => by simp at h
  | a :: b :: tl, h => by
      have htl : Even tl.length := by
        simp only [List.length_cons] at h
        rcases h with ⟨k, hk⟩
        exact ⟨k - 1, by omega⟩
      have hpair : cGen R n a * cGen R n b ∈ CliffordAlgebra.even (cliffordNegSqForm R n) := by
        change cGen R n a * cGen R n b ∈
          Subalgebra.toSubmodule (CliffordAlgebra.even (cliffordNegSqForm R n))
        rw [CliffordAlgebra.even_toSubmodule]
        exact CliffordAlgebra.ι_mul_ι_mem_evenOdd_zero _ _ _
      rw [List.map_cons, List.map_cons, List.prod_cons, List.prod_cons, ← mul_assoc]
      exact Subalgebra.mul_mem _ hpair (listProd_even_mem_even R tl htl)

theorem kUnit_mem_even (R : Type*) [CommRing R] (m : ℕ) (r : Fin (2 * m + 1)) :
    kUnit R m r ∈ CliffordAlgebra.even (cliffordNegSqForm R (2 * m + 1)) := by
  have hev : Even ((bladeList (Finset.univ : Finset (Fin (2 * m + 1))) ++ [r]).length) := by
    simp only [List.length_append, bladeList_length, Finset.card_univ, Fintype.card_fin,
      List.length_singleton]
    exact ⟨m + 1, by ring⟩
  have hprod : (((bladeList (Finset.univ : Finset (Fin (2 * m + 1))) ++ [r]).map
      (cGen R (2 * m + 1))).prod) = kUnit R m r := by
    simp [kUnit, ωOdd, cBlade]
  rw [← hprod]
  exact listProd_even_mem_even R _ hev

/-- Clifford's odd-algebra total generator product (`p. 356`):
`k₁ k₂ ⋯ k_{2m+1} = (-1)^(m+1)` (`-1` for `m` even, `+1` for `m` odd). -/
theorem kUnit_prod_univ (R : Type*) [CommRing R] (m : ℕ) :
    ((List.finRange (2 * m + 1)).map (kUnit R m)).prod = ((-1 : R) ^ (m + 1)) • 1 := by
  have hfactor : ∀ L : List (Fin (2 * m + 1)),
      (L.map (kUnit R m)).prod =
        (ωOdd R m) ^ L.length * (L.map (cGen R (2 * m + 1))).prod := by
    intro L
    induction L with
    | nil => simp
    | cons a tl ih =>
        have hpow_comm : cGen R (2 * m + 1) a * (ωOdd R m) ^ tl.length =
            (ωOdd R m) ^ tl.length * cGen R (2 * m + 1) a := by
          induction tl.length with
          | zero => simp
          | succ k ihk =>
              calc
                cGen R (2 * m + 1) a * (ωOdd R m) ^ (k + 1)
                    = (cGen R (2 * m + 1) a * ωOdd R m) * (ωOdd R m) ^ k := by
                      rw [pow_succ', mul_assoc]
                _ = (ωOdd R m * cGen R (2 * m + 1) a) * (ωOdd R m) ^ k := by
                      rw [ωOdd_comm_cGen]
                _ = ωOdd R m * (cGen R (2 * m + 1) a * (ωOdd R m) ^ k) := by rw [mul_assoc]
                _ = ωOdd R m * ((ωOdd R m) ^ k * cGen R (2 * m + 1) a) := by rw [ihk]
                _ = (ωOdd R m) ^ (k + 1) * cGen R (2 * m + 1) a := by
                      rw [← mul_assoc, ← pow_succ']
        calc
          ((a :: tl).map (kUnit R m)).prod
              = (ωOdd R m * cGen R (2 * m + 1) a) * ((tl.map (kUnit R m)).prod) := by
                simp [kUnit]
          _ = ωOdd R m * (cGen R (2 * m + 1) a * (ωOdd R m) ^ tl.length) *
                (tl.map (cGen R (2 * m + 1))).prod := by
                rw [ih]; noncomm_ring
          _ = ωOdd R m * ((ωOdd R m) ^ tl.length * cGen R (2 * m + 1) a) *
                (tl.map (cGen R (2 * m + 1))).prod := by
                rw [hpow_comm]
          _ = (ωOdd R m) ^ (a :: tl).length * ((a :: tl).map (cGen R (2 * m + 1))).prod := by
                simp only [List.length_cons, pow_succ', List.map_cons, List.prod_cons, mul_assoc]
  rw [hfactor (List.finRange (2 * m + 1)), List.length_finRange]
  have hω_list : ((List.finRange (2 * m + 1)).map (cGen R (2 * m + 1))).prod = ωOdd R m := by
    simp [ωOdd, cBlade, bladeList]
  rw [hω_list, ← pow_succ]
  have h2m : 2 * m + 1 + 1 = 2 * (m + 1) := by ring
  rw [h2m, pow_mul, pow_two, ωOdd_sq]
  have hsmul_pow : ∀ (c : R) (n : ℕ),
      (c • (1 : CliffordAlgebra (cliffordNegSqForm R (2 * m + 1)))) ^ n = (c ^ n) • 1 := by
    intro c n
    induction n with
    | zero => simp
    | succ k ihk => rw [pow_succ, ihk, smul_mul_smul_comm, one_mul, pow_succ]
  have hsmul : (((-1 : R) ^ (m + 1)) • (1 : CliffordAlgebra (cliffordNegSqForm R (2 * m + 1)))) ^
      (m + 1) = ((-1 : R) ^ ((m + 1) * (m + 1))) • 1 := by
    rw [hsmul_pow, ← pow_mul]
  have hmod : (m + 1) * (m + 1) ≡ m + 1 [MOD 2] := by
    have hmul : (m + 1) * (m + 1) = m * (m + 1) + (m + 1) := by ring
    have hev : 2 ∣ m * (m + 1) := by
      rcases Nat.even_or_odd m with ⟨j, hj⟩ | ⟨j, hj⟩
      · exact ⟨j * (m + 1), by rw [hj]; ring⟩
      · exact ⟨m * (j + 1), by rw [hj]; ring⟩
    rw [hmul, Nat.ModEq]; omega
  rw [hsmul, neg_one_pow_eq_of_modEq hmod]

/-- Explicit `Cl(0, 5)` split-quaternion zero-divisor witness (`C-CL1`, `p. 356`, `m = 2`):
`(1 + k₀)(1 - k₀) = 0` while `1 + k₀ ≠ 0` and `1 - k₀ ≠ 0`. -/
theorem fiveWay_split_quaternion_zero_divisors :
    (1 + kUnit ℝ 2 0) * (1 - kUnit ℝ 2 0) = 0 ∧
      1 + kUnit ℝ 2 0 ≠ 0 ∧ 1 - kUnit ℝ 2 0 ≠ 0 := by
  have hk_sq : kUnit ℝ 2 0 * kUnit ℝ 2 0 = 1 := by
    rw [kUnit_sq ℝ 2 0]; simp
  have hprod : (1 + kUnit ℝ 2 0) * (1 - kUnit ℝ 2 0) = 0 := by
    calc
      (1 + kUnit ℝ 2 0) * (1 - kUnit ℝ 2 0) = 1 - kUnit ℝ 2 0 * kUnit ℝ 2 0 := by noncomm_ring
      _ = 0 := by rw [hk_sq, sub_self]
  have hk_eq : kUnit ℝ 2 0 = -cBlade ℝ 5 {1, 2, 3, 4} := by
    have h0_mem : bladeList (Finset.univ : Finset (Fin 5)) = [0, 1, 2, 3, 4] := by decide
    have h1234 : bladeList ({1, 2, 3, 4} : Finset (Fin 5)) = [1, 2, 3, 4] := by decide
    have hcomm : cGen ℝ 5 0 * (cBlade ℝ 5 {1, 2, 3, 4}) =
        (cBlade ℝ 5 {1, 2, 3, 4}) * cGen ℝ 5 0 := by
      have hcm := cGen_mul_cBlade ℝ 5 0 {1, 2, 3, 4}
      have hcard : ({1, 2, 3, 4} : Finset (Fin 5)).card = 4 := by decide
      have hnot : (0 : Fin 5) ∉ ({1, 2, 3, 4} : Finset (Fin 5)) := by decide
      simp [hcard, hnot] at hcm
      norm_num at hcm
      exact hcm
    calc
      kUnit ℝ 2 0 = (cGen ℝ 5 0 * cBlade ℝ 5 {1, 2, 3, 4}) * cGen ℝ 5 0 := by
        simp [kUnit, ωOdd, cBlade, h0_mem, h1234, mul_assoc]
      _ = (cBlade ℝ 5 {1, 2, 3, 4} * cGen ℝ 5 0) * cGen ℝ 5 0 := by rw [hcomm]
      _ = cBlade ℝ 5 {1, 2, 3, 4} * (cGen ℝ 5 0 * cGen ℝ 5 0) := mul_assoc _ _ _
      _ = -cBlade ℝ 5 {1, 2, 3, 4} := by rw [cGen_sq]; noncomm_ring
  have hcoord : bladeRepr ℝ 5 (1 + kUnit ℝ 2 0) ∅ = 1 ∧
      bladeRepr ℝ 5 (1 - kUnit ℝ 2 0) ∅ = 1 := by
    have h1 : (1 : CliffordAlgebra (cliffordNegSqForm ℝ 5)) = cBlade ℝ 5 ∅ := (cBlade_empty ℝ 5).symm
    have hne : (∅ : Finset (Fin 5)) ≠ {1, 2, 3, 4} := by decide
    constructor
    · rw [hk_eq, h1, bladeRepr, map_add, map_neg, LinearMap.add_apply, LinearMap.neg_apply,
        Pi.add_apply, Pi.neg_apply]
      change bladeRepr ℝ 5 (cBlade ℝ 5 ∅) ∅ + -(bladeRepr ℝ 5 (cBlade ℝ 5 {1, 2, 3, 4}) ∅) = 1
      rw [bladeRepr_cBlade, bladeRepr_cBlade]
      simp [hne]
    · rw [hk_eq, sub_neg_eq_add, h1, bladeRepr, map_add, LinearMap.add_apply, Pi.add_apply]
      change bladeRepr ℝ 5 (cBlade ℝ 5 ∅) ∅ + bladeRepr ℝ 5 (cBlade ℝ 5 {1, 2, 3, 4}) ∅ = 1
      rw [bladeRepr_cBlade, bladeRepr_cBlade]
      simp [hne]
  refine ⟨hprod, ?_, ?_⟩
  · intro hz
    have hc := congrArg (fun X => bladeRepr ℝ 5 X ∅) hz
    rw [hcoord.1, bladeRepr, map_zero, LinearMap.zero_apply, Pi.zero_apply] at hc
    norm_num at hc
  · intro hz
    have hc := congrArg (fun X => bladeRepr ℝ 5 X ∅) hz
    rw [hcoord.2, bladeRepr, map_zero, LinearMap.zero_apply, Pi.zero_apply] at hc
    norm_num at hc

end OddWayGenerators

section KBladesAndAllMQuaternionFactorization

/-- Ordered product of `kUnit R m` generators over `K : Finset (Fin (2m+1))`. -/
def kBlade (R : Type*) [CommRing R] (m : ℕ) (K : Finset (Fin (2 * m + 1))) :
    CliffordAlgebra (cliffordNegSqForm R (2 * m + 1)) :=
  ((bladeList K).map (kUnit R m)).prod

@[simp]
theorem kBlade_empty (R : Type*) [CommRing R] (m : ℕ) :
    kBlade R m ∅ = 1 := by
  unfold kBlade
  have hnil : bladeList (∅ : Finset (Fin (2 * m + 1))) = [] := by
    rw [bladeList]
    simp
  rw [hnil, List.map_nil, List.prod_nil]

theorem kBlade_mem_even (R : Type*) [CommRing R] (m : ℕ) (K : Finset (Fin (2 * m + 1))) :
    kBlade R m K ∈ CliffordAlgebra.even (cliffordNegSqForm R (2 * m + 1)) := by
  simp only [kBlade]
  induction (bladeList K) with
  | nil => simp only [List.map_nil, List.prod_nil]; exact Subalgebra.one_mem _
  | cons r tl ih =>
      rw [List.map_cons, List.prod_cons]
      exact Subalgebra.mul_mem _ (kUnit_mem_even R m r) ih

private lemma kUnit_mul_listProd_of_nodup (R : Type*) [CommRing R] (m : ℕ)
    (r : Fin (2 * m + 1)) :
    ∀ L : List (Fin (2 * m + 1)), L.Nodup →
      kUnit R m r * ((L.map (kUnit R m)).prod) =
        ((-1 : R) ^ (L.length + if r ∈ L then 1 else 0)) •
          (((L.map (kUnit R m)).prod) * kUnit R m r)
  | [], _ => by simp
  | a :: tl, hnd => by
      have ha_not : a ∉ tl := (List.nodup_cons.mp hnd).1
      have htl : tl.Nodup := (List.nodup_cons.mp hnd).2
      have ih := kUnit_mul_listProd_of_nodup R m r tl htl
      by_cases hra : r = a
      · subst hra
        have ih' : kUnit R m r * ((tl.map (kUnit R m)).prod) =
            ((-1 : R) ^ tl.length) • (((tl.map (kUnit R m)).prod) * kUnit R m r) := by
          simpa [ha_not] using ih
        have hmod : tl.length + 2 ≡ tl.length [MOD 2] := by rw [Nat.ModEq]; omega
        have hpow : (-1 : R) ^ (tl.length + 2) = (-1 : R) ^ tl.length :=
          neg_one_pow_eq_of_modEq hmod
        have hid : kUnit R m r * (((kUnit R m r :: tl.map (kUnit R m)).prod)) =
            ((-1 : R) ^ tl.length) • (((kUnit R m r :: tl.map (kUnit R m)).prod) * kUnit R m r) := by
          calc
            kUnit R m r * (((kUnit R m r :: tl.map (kUnit R m)).prod))
                = kUnit R m r * (kUnit R m r * ((tl.map (kUnit R m)).prod)) := by
                  simp only [List.prod_cons]
            _ = kUnit R m r * (((-1 : R) ^ tl.length) • (((tl.map (kUnit R m)).prod) * kUnit R m r)) := by
                  rw [ih']
            _ = ((-1 : R) ^ tl.length) • ((kUnit R m r * ((tl.map (kUnit R m)).prod)) * kUnit R m r) := by
                  rw [mul_smul_comm, mul_assoc]
            _ = ((-1 : R) ^ tl.length) • (((kUnit R m r :: tl.map (kUnit R m)).prod) * kUnit R m r) := by
                  simp only [List.prod_cons]
        simpa [hpow] using hid
      · have hcomm := kUnit_anticomm R m hra
        have hmem_iff : (r ∈ a :: tl) ↔ r ∈ tl := by simp [hra]
        calc
          kUnit R m r * ((kUnit R m a :: tl.map (kUnit R m)).prod)
              = (kUnit R m r * kUnit R m a) * ((tl.map (kUnit R m)).prod) := by
                simp [List.prod_cons, mul_assoc]
          _ = -(kUnit R m a * kUnit R m r) * ((tl.map (kUnit R m)).prod) := by rw [hcomm]
          _ = -(kUnit R m a * (kUnit R m r * ((tl.map (kUnit R m)).prod))) := by noncomm_ring
          _ = -(kUnit R m a * ((-1 : R) ^ (tl.length + if r ∈ tl then 1 else 0) •
                (((tl.map (kUnit R m)).prod) * kUnit R m r))) := by rw [ih]
          _ = ((-1 : R) ^ (tl.length + 1 + if r ∈ a :: tl then 1 else 0)) •
                (((kUnit R m a :: tl.map (kUnit R m)).prod) * kUnit R m r) := by
                simp only [hmem_iff]
                have hexp : tl.length + 1 + (if r ∈ tl then 1 else 0) =
                    (tl.length + if r ∈ tl then 1 else 0) + 1 := by ring
                rw [hexp, pow_succ, mul_neg_one, neg_smul, mul_smul_comm]
                simp [List.prod_cons, mul_assoc]

private lemma kListProd_mul_swap_aux (R : Type*) [CommRing R] (m : ℕ)
    (L : List (Fin (2 * m + 1))) (hL : L.Nodup) :
    ∀ K : List (Fin (2 * m + 1)), K.Nodup →
      ((K.map (kUnit R m)).prod) * ((L.map (kUnit R m)).prod) =
        ((-1 : R) ^ (K.length * L.length + (K.toFinset ∩ L.toFinset).card)) •
          (((L.map (kUnit R m)).prod) * ((K.map (kUnit R m)).prod))
  | [], _ => by simp
  | a :: tl, hK => by
      have ha_not : a ∉ tl := (List.nodup_cons.mp hK).1
      have htl : tl.Nodup := (List.nodup_cons.mp hK).2
      have ih := kListProd_mul_swap_aux R m L hL tl htl
      have hmove := kUnit_mul_listProd_of_nodup R m a L hL
      have hcard_inter :
          ((insert a tl.toFinset) ∩ L.toFinset).card =
            (tl.toFinset ∩ L.toFinset).card + (if a ∈ L then 1 else 0) := by
        by_cases haL : a ∈ L
        · have haL' : a ∈ L.toFinset := List.mem_toFinset.mpr haL
          have hnot_inter : a ∉ tl.toFinset ∩ L.toFinset := by simp [List.mem_toFinset, ha_not]
          have hins : (insert a tl.toFinset) ∩ L.toFinset =
              insert a (tl.toFinset ∩ L.toFinset) := by ext x; simp [haL']
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
        ((a :: tl).map (kUnit R m)).prod * ((L.map (kUnit R m)).prod)
            = kUnit R m a * (((tl.map (kUnit R m)).prod) * ((L.map (kUnit R m)).prod)) := by
              simp [List.prod_cons, mul_assoc]
        _ = ((-1 : R) ^ (tl.length * L.length + (tl.toFinset ∩ L.toFinset).card)) •
              ((kUnit R m a * ((L.map (kUnit R m)).prod)) * ((tl.map (kUnit R m)).prod)) := by
              rw [ih, mul_smul_comm, mul_assoc]
        _ = ((-1 : R) ^ ((a :: tl).length * L.length + ((a :: tl).toFinset ∩ L.toFinset).card)) •
              (((L.map (kUnit R m)).prod) * (((a :: tl).map (kUnit R m)).prod)) := by
              rw [hmove, smul_mul_assoc, smul_smul, ← pow_add]
              simp only [List.toFinset_cons, hcard_inter, List.length_cons, add_mul, one_mul,
                List.map_cons, List.prod_cons, ← mul_assoc]
              congr 2
              ring

/-- Overlap commutation law for `k`-blades (`pp. 356–357`):
`kBlade K₁ * kBlade K₂ = (-1)^(|K₁|*|K₂| + |K₁ ∩ K₂|) • (kBlade K₂ * kBlade K₁)`. -/
theorem kBlade_mul_swap (R : Type*) [CommRing R] (m : ℕ)
    (K₁ K₂ : Finset (Fin (2 * m + 1))) :
    kBlade R m K₁ * kBlade R m K₂ =
      ((-1 : R) ^ (K₁.card * K₂.card + (K₁ ∩ K₂).card)) •
        (kBlade R m K₂ * kBlade R m K₁) := by
  simpa [kBlade, bladeList_length, bladeList_toFinset] using
    kListProd_mul_swap_aux R m (bladeList K₂) (bladeList_nodup K₂)
      (bladeList K₁) (bladeList_nodup K₁)

theorem kBlade_commute_of_even (R : Type*) [CommRing R] (m : ℕ)
    {K₁ K₂ : Finset (Fin (2 * m + 1))}
    (he : Even (K₁.card * K₂.card + (K₁ ∩ K₂).card)) :
    Commute (kBlade R m K₁) (kBlade R m K₂) := by
  change kBlade R m K₁ * kBlade R m K₂ = kBlade R m K₂ * kBlade R m K₁
  rw [kBlade_mul_swap]
  rcases he with ⟨k, hk⟩
  rw [hk, ← two_mul, pow_mul]
  simp

private lemma kListProd_sq_of_nodup (R : Type*) [CommRing R] (m : ℕ) :
    ∀ L : List (Fin (2 * m + 1)), L.Nodup →
      ((L.map (kUnit R m)).prod) * ((L.map (kUnit R m)).prod) =
        ((-1 : R) ^ (m * L.length + L.length * (L.length - 1) / 2)) • 1
  | [], _ => by simp
  | a :: tl, hnd => by
      have ha_not : a ∉ tl := (List.nodup_cons.mp hnd).1
      have htl : tl.Nodup := (List.nodup_cons.mp hnd).2
      have ih := kListProd_sq_of_nodup R m tl htl
      have hswap := kUnit_mul_listProd_of_nodup R m a tl htl
      simp [ha_not] at hswap
      have hmove : ((tl.map (kUnit R m)).prod) * kUnit R m a =
          ((-1 : R) ^ tl.length) • (kUnit R m a * ((tl.map (kUnit R m)).prod)) := by
        calc
          ((tl.map (kUnit R m)).prod) * kUnit R m a
              = (((-1 : R) ^ tl.length) * ((-1 : R) ^ tl.length)) •
                  (((tl.map (kUnit R m)).prod) * kUnit R m a) := by
                have h1 : (-1 : R) ^ tl.length * (-1 : R) ^ tl.length = 1 := by
                  rw [← pow_add, ← two_mul, pow_mul]; simp
                rw [h1, one_smul]
          _ = ((-1 : R) ^ tl.length) • (kUnit R m a * ((tl.map (kUnit R m)).prod)) := by
                rw [mul_smul, ← hswap]
      have htri : m * (tl.length + 1) + (tl.length + 1) * tl.length / 2 =
          m + tl.length + (m * tl.length + tl.length * (tl.length - 1) / 2) := by
        have hstep : (tl.length + 1) * tl.length / 2 = tl.length * (tl.length - 1) / 2 + tl.length := by
          cases tl with
          | nil => simp
          | cons b tl' =>
              have hdiv : 2 ∣ (tl'.length + 1) * tl'.length := by
                rcases Nat.even_or_odd tl'.length with ⟨j, hj⟩ | ⟨j, hj⟩
                · exact ⟨(tl'.length + 1) * j, by rw [hj]; ring⟩
                · exact ⟨(j + 1) * tl'.length, by rw [hj]; ring⟩
              have hnum : (tl'.length + 2) * (tl'.length + 1) =
                  (tl'.length + 1) * tl'.length + 2 * (tl'.length + 1) := by ring
              simp only [List.length_cons, Nat.add_sub_cancel]
              rw [hnum, Nat.add_div_of_dvd_right hdiv, Nat.mul_div_right _ (by decide)]
        rw [hstep]
        ring
      calc
        (((a :: tl).map (kUnit R m)).prod) * (((a :: tl).map (kUnit R m)).prod)
            = kUnit R m a * ((((tl.map (kUnit R m)).prod) * kUnit R m a) *
                ((tl.map (kUnit R m)).prod)) := by
              simp [List.prod_cons, mul_assoc]
        _ = ((-1 : R) ^ tl.length) •
              ((kUnit R m a * kUnit R m a) *
                (((tl.map (kUnit R m)).prod) * ((tl.map (kUnit R m)).prod))) := by
              rw [hmove, smul_mul_assoc, mul_smul_comm, mul_assoc, mul_assoc]
        _ = ((-1 : R) ^ (m + tl.length)) •
              (((tl.map (kUnit R m)).prod) * ((tl.map (kUnit R m)).prod)) := by
              rw [kUnit_sq, smul_mul_assoc, one_mul, smul_smul, ← pow_add,
                add_comm tl.length m]
        _ = ((-1 : R) ^ (m * (a :: tl).length + (a :: tl).length * ((a :: tl).length - 1) / 2)) • 1 := by
              rw [ih, smul_smul, ← pow_add]
              simp only [List.length_cons, Nat.add_sub_cancel, htri]

theorem kBlade_sq (R : Type*) [CommRing R] (m : ℕ) (K : Finset (Fin (2 * m + 1))) :
    kBlade R m K * kBlade R m K =
      ((-1 : R) ^ (m * K.card + K.card * (K.card - 1) / 2)) • 1 := by
  simpa [kBlade, bladeList_length] using
    kListProd_sq_of_nodup R m (bladeList K) (bladeList_nodup K)

private lemma listProd_kUnit_eq_pow_ω_mul_cBlade (R : Type*) [CommRing R] (m : ℕ)
    (K : Finset (Fin (2 * m + 1))) :
    kBlade R m K = (ωOdd R m) ^ K.card * cBlade R (2 * m + 1) K := by
  have hfactor : ∀ L : List (Fin (2 * m + 1)),
      (L.map (kUnit R m)).prod =
        (ωOdd R m) ^ L.length * (L.map (cGen R (2 * m + 1))).prod := by
    intro L
    induction L with
    | nil => simp
    | cons a tl ih =>
        have hpow_comm : cGen R (2 * m + 1) a * (ωOdd R m) ^ tl.length =
            (ωOdd R m) ^ tl.length * cGen R (2 * m + 1) a := by
          induction tl.length with
          | zero => simp
          | succ k ihk =>
              calc
                cGen R (2 * m + 1) a * (ωOdd R m) ^ (k + 1)
                    = (cGen R (2 * m + 1) a * ωOdd R m) * (ωOdd R m) ^ k := by
                      rw [pow_succ', mul_assoc]
                _ = (ωOdd R m * cGen R (2 * m + 1) a) * (ωOdd R m) ^ k := by
                      rw [ωOdd_comm_cGen]
                _ = ωOdd R m * (cGen R (2 * m + 1) a * (ωOdd R m) ^ k) := by rw [mul_assoc]
                _ = ωOdd R m * ((ωOdd R m) ^ k * cGen R (2 * m + 1) a) := by rw [ihk]
                _ = (ωOdd R m) ^ (k + 1) * cGen R (2 * m + 1) a := by
                      rw [← mul_assoc, ← pow_succ']
        calc
          ((a :: tl).map (kUnit R m)).prod
              = (ωOdd R m * cGen R (2 * m + 1) a) * ((tl.map (kUnit R m)).prod) := by
                simp [kUnit]
          _ = ωOdd R m * (cGen R (2 * m + 1) a * (ωOdd R m) ^ tl.length) *
                (tl.map (cGen R (2 * m + 1))).prod := by rw [ih]; noncomm_ring
          _ = ωOdd R m * ((ωOdd R m) ^ tl.length * cGen R (2 * m + 1) a) *
                (tl.map (cGen R (2 * m + 1))).prod := by rw [hpow_comm]
          _ = (ωOdd R m) ^ (a :: tl).length * ((a :: tl).map (cGen R (2 * m + 1))).prod := by
                simp only [List.length_cons, pow_succ', List.map_cons, List.prod_cons, mul_assoc]
  simpa [kBlade, cBlade, bladeList_length] using hfactor (bladeList K)

private def toggleSorted {n : ℕ} (r : Fin n) : List (Fin n) → List (Fin n)
  | [] => [r]
  | a :: tl => if r < a then r :: a :: tl else if r = a then tl else a :: toggleSorted r tl

private lemma mem_toggleSorted_subset {n : ℕ} {r x : Fin n} :
    ∀ L : List (Fin n), x ∈ toggleSorted r L → x = r ∨ x ∈ L
  | [] => by simp [toggleSorted]
  | a :: tl => by
      dsimp only [toggleSorted]
      split_ifs
      · simp
      · intro hx; exact Or.inr (List.mem_cons_of_mem a hx)
      · simp only [List.mem_cons]
        rintro (rfl | hx)
        · exact Or.inr (Or.inl rfl)
        · rcases mem_toggleSorted_subset tl hx with rfl | hx'
          · exact Or.inl rfl
          · exact Or.inr (Or.inr hx')

private lemma toggleSorted_pairwise_lt {n : ℕ} (r : Fin n) :
    ∀ L : List (Fin n), L.Pairwise (· < ·) → (toggleSorted r L).Pairwise (· < ·)
  | [], _ => by simp [toggleSorted]
  | a :: tl, hL => by
      have ha : ∀ b ∈ tl, a < b := (List.pairwise_cons.mp hL).1
      have htl : tl.Pairwise (· < ·) := (List.pairwise_cons.mp hL).2
      dsimp only [toggleSorted]
      split_ifs with h1 h2
      · rw [List.pairwise_cons]
        refine ⟨?_, hL⟩
        intro b hb
        simp only [List.mem_cons] at hb
        rcases hb with rfl | hb
        · exact h1
        · exact lt_trans h1 (ha b hb)
      · exact htl
      · have har : a < r := lt_of_le_of_ne (not_lt.mp h1) (Ne.symm h2)
        rw [List.pairwise_cons]
        refine ⟨?_, toggleSorted_pairwise_lt r tl htl⟩
        intro b hb
        rcases mem_toggleSorted_subset tl hb with rfl | hb'
        · exact har
        · exact ha b hb'

private lemma toggleSorted_toFinset {n : ℕ} (r : Fin n) :
    ∀ L : List (Fin n), L.Pairwise (· < ·) →
      (toggleSorted r L).toFinset = symmDiff {r} L.toFinset
  | [], _ => by
      ext x; simp [toggleSorted, Finset.mem_symmDiff]
  | a :: tl, hL => by
      have ha : ∀ b ∈ tl, a < b := (List.pairwise_cons.mp hL).1
      have htl : tl.Pairwise (· < ·) := (List.pairwise_cons.mp hL).2
      have ha_not : a ∉ tl := fun h => lt_irrefl a (ha a h)
      dsimp only [toggleSorted]
      split_ifs with h1 h2
      · have hr_not : r ∉ tl := fun h => lt_irrefl r (lt_trans h1 (ha r h))
        ext x
        simp only [List.toFinset_cons, Finset.mem_insert, List.mem_toFinset, Finset.mem_symmDiff,
          Finset.mem_singleton]
        by_cases hxr : x = r
        · subst hxr; simp [h1.ne, hr_not]
        · simp [hxr]
      · subst h2
        ext x
        simp only [List.toFinset_cons, List.mem_toFinset, Finset.mem_symmDiff, Finset.mem_singleton,
          Finset.mem_insert]
        by_cases hxr : x = r <;> simp [hxr, ha_not]
      · have har : a < r := lt_of_le_of_ne (not_lt.mp h1) (Ne.symm h2)
        have ih := toggleSorted_toFinset r tl htl
        ext x
        rw [List.toFinset_cons, ih]
        simp only [List.toFinset_cons, Finset.mem_insert, Finset.mem_symmDiff, Finset.mem_singleton,
          List.mem_toFinset]
        by_cases hxa : x = a
        · subst hxa; simp [har.ne]
        · simp [hxa]

private lemma toggleSorted_bladeList {n : ℕ} (r : Fin n) (S : Finset (Fin n)) :
    toggleSorted r (bladeList S) = bladeList (symmDiff {r} S) := by
  have hp1 : (toggleSorted r (bladeList S)).Pairwise (· < ·) :=
    toggleSorted_pairwise_lt r (bladeList S) (bladeList_pairwise_lt S)
  refine hp1.eq_of_mem_iff (bladeList_pairwise_lt (symmDiff {r} S)) fun x => ?_
  rw [← List.mem_toFinset, ← List.mem_toFinset,
    toggleSorted_toFinset r (bladeList S) (bladeList_pairwise_lt S),
    bladeList_toFinset, bladeList_toFinset]

private lemma unit_mul_listProd_toggle {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (n : ℕ) (f : Fin n → A) (uSq : ℤˣ)
    (hsq : ∀ r : Fin n, f r * f r = ((uSq : ℤ) : R) • (1 : A))
    (hanti : ∀ {r s : Fin n}, r ≠ s → f r * f s = -(f s * f r))
    (r : Fin n) :
    ∀ L : List (Fin n), L.Pairwise (· < ·) →
      ∃ s : ℤˣ, f r * ((L.map f).prod) = ((s : ℤ) : R) • (((toggleSorted r L).map f).prod)
  | [], _ => ⟨1, by simp [toggleSorted]⟩
  | a :: tl, hL => by
      have htl : tl.Pairwise (· < ·) := (List.pairwise_cons.mp hL).2
      dsimp only [toggleSorted]
      split_ifs with h1 h2
      · refine ⟨1, by simp⟩
      · subst h2
        refine ⟨uSq, ?_⟩
        simp only [List.map_cons, List.prod_cons, ← mul_assoc, hsq r, smul_mul_assoc, one_mul]
      · have ih := unit_mul_listProd_toggle n f uSq hsq hanti r tl htl
        rcases ih with ⟨s, hs⟩
        have har : r ≠ a := h2
        refine ⟨-s, ?_⟩
        calc
          f r * (((a :: tl).map f).prod)
              = (f r * f a) * ((tl.map f).prod) := by simp [List.prod_cons, mul_assoc]
          _ = -(f a * f r) * ((tl.map f).prod) := by rw [hanti har]
          _ = -(f a * (f r * ((tl.map f).prod))) := by noncomm_ring
          _ = -(f a * (((s : ℤ) : R) • (((toggleSorted r tl).map f).prod))) := by rw [hs]
          _ = (((-s : ℤˣ) : ℤ) : R) • (((a :: toggleSorted r tl).map f).prod) := by
              simp [neg_smul, List.prod_cons]

private lemma listProd_mul_signed_symmDiff {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (n : ℕ) (f : Fin n → A) (uSq : ℤˣ)
    (hsq : ∀ r : Fin n, f r * f r = ((uSq : ℤ) : R) • (1 : A))
    (hanti : ∀ {r s : Fin n}, r ≠ s → f r * f s = -(f s * f r))
    (S₂ : Finset (Fin n)) :
    ∀ L : List (Fin n), L.Nodup →
      ∃ s : ℤˣ, ((L.map f).prod) * (((bladeList S₂).map f).prod) =
        ((s : ℤ) : R) • (((bladeList (symmDiff L.toFinset S₂)).map f).prod)
  | [], _ => ⟨1, by
      have hempty : symmDiff (∅ : Finset (Fin n)) S₂ = S₂ := by
        ext x; simp [Finset.mem_symmDiff]
      simp [hempty]⟩
  | a :: tl, hnd => by
      have ha_not : a ∉ tl := (List.nodup_cons.mp hnd).1
      have htl : tl.Nodup := (List.nodup_cons.mp hnd).2
      rcases listProd_mul_signed_symmDiff n f uSq hsq hanti S₂ tl htl with ⟨s₁, hs₁⟩
      rcases unit_mul_listProd_toggle n f uSq hsq hanti a
        (bladeList (symmDiff tl.toFinset S₂)) (bladeList_pairwise_lt _) with ⟨s₂, hs₂⟩
      rw [toggleSorted_bladeList] at hs₂
      have hset : symmDiff {a} (symmDiff tl.toFinset S₂) = symmDiff (a :: tl).toFinset S₂ := by
        have hins : (a :: tl).toFinset = symmDiff {a} tl.toFinset := by
          ext x
          simp only [List.toFinset_cons, Finset.mem_insert, List.mem_toFinset,
            Finset.mem_symmDiff, Finset.mem_singleton]
          by_cases hxa : x = a <;> simp [hxa, ha_not]
        rw [hins, symmDiff_assoc]
      refine ⟨s₁ * s₂, ?_⟩
      calc
        ((a :: tl).map f).prod * ((bladeList S₂).map f).prod
            = f a * (((tl.map f).prod) * ((bladeList S₂).map f).prod) := by
              simp [List.prod_cons, mul_assoc]
        _ = f a * (((s₁ : ℤ) : R) • (((bladeList (symmDiff tl.toFinset S₂)).map f).prod)) := by
              rw [hs₁]
        _ = ((s₁ : ℤ) : R) • (f a * ((bladeList (symmDiff tl.toFinset S₂)).map f).prod) := by
              rw [mul_smul_comm]
        _ = ((s₁ : ℤ) : R) • (((s₂ : ℤ) : R) •
              ((bladeList (symmDiff {a} (symmDiff tl.toFinset S₂))).map f).prod) := by
              rw [hs₂]
        _ = (((s₁ * s₂ : ℤˣ) : ℤ) : R) • ((bladeList (symmDiff (a :: tl).toFinset S₂)).map f).prod := by
              rw [smul_smul, Units.val_mul, Int.cast_mul, hset]

theorem cBlade_mul_cBlade_eq_signed_symmDiff (R : Type*) [CommRing R] (n : ℕ)
    (S₁ S₂ : Finset (Fin n)) :
    ∃ s : ℤˣ, cBlade R n S₁ * cBlade R n S₂ = ((s : ℤ) : R) • cBlade R n (symmDiff S₁ S₂) := by
  have hsq' : ∀ r : Fin n, cGen R n r * cGen R n r = (((-1 : ℤˣ) : ℤ) : R) • (1 : CliffordAlgebra _) := by
    intro r
    rw [cGen_sq R n r]
    simp
  simpa [cBlade, bladeList_toFinset] using
    listProd_mul_signed_symmDiff n (cGen R n) (-1) hsq'
      (fun {r s} hrs => cGen_anticomm hrs) S₂ (bladeList S₁) (bladeList_nodup S₁)

private lemma ωOdd_mul_cBlade_eq_signed_compl (R : Type*) [CommRing R] (m : ℕ)
    (K : Finset (Fin (2 * m + 1))) :
    ∃ s : ℤˣ, ωOdd R m * cBlade R (2 * m + 1) K = ((s : ℤ) : R) • cBlade R (2 * m + 1) Kᶜ := by
  have hsym : symmDiff (Finset.univ : Finset (Fin (2 * m + 1))) K = Kᶜ := by
    ext x; simp [Finset.mem_symmDiff]
  simpa [ωOdd, hsym] using
    cBlade_mul_cBlade_eq_signed_symmDiff R (2 * m + 1) Finset.univ K

/-- Canonical even-parity support representative of a `k`-blade (`p. 358`):
`K` if `K.card` is even, or `Kᶜ` if `K.card` is odd. -/
def toEvenBlade (m : ℕ) (K : Finset (Fin (2 * m + 1))) : Finset (Fin (2 * m + 1)) :=
  if Even K.card then K else Kᶜ

theorem toEvenBlade_card_even (m : ℕ) (K : Finset (Fin (2 * m + 1))) :
    Even (toEvenBlade m K).card := by
  dsimp only [toEvenBlade]
  split_ifs with he
  · exact he
  · have hc := Finset.card_compl_add_card K
    simp only [Fintype.card_fin] at hc
    rw [Nat.not_even_iff_odd] at he
    rcases he with ⟨j, hj⟩
    exact ⟨m - j, by omega⟩

theorem kBlade_eq_signed_cBlade_toEvenBlade (R : Type*) [CommRing R] (m : ℕ)
    (K : Finset (Fin (2 * m + 1))) :
    ∃ s : ℤˣ, kBlade R m K = ((s : ℤ) : R) • cBlade R (2 * m + 1) (toEvenBlade m K) := by
  rw [listProd_kUnit_eq_pow_ω_mul_cBlade]
  have hsq : ωOdd R m * ωOdd R m = ((((-1 : ℤˣ) ^ (m + 1) : ℤˣ) : ℤ) : R) • 1 := by
    rw [ωOdd_sq]
    simp
  have hpow : ∀ k : ℕ, (ωOdd R m) ^ (2 * k) =
      (((((-1 : ℤˣ) ^ ((m + 1) * k) : ℤˣ) : ℤ) : R)) • 1 := by
    intro k
    induction k with
    | zero => simp
    | succ j ih =>
        rw [Nat.mul_add, mul_one, pow_add, pow_two, ih, hsq, smul_mul_smul_comm, mul_one,
          ← Int.cast_mul, ← Units.val_mul, ← pow_add,
          show (m + 1) * j + (m + 1) = (m + 1) * (j + 1) by ring]
  by_cases he : Even K.card
  · rcases he with ⟨q, hq⟩
    have hcard : K.card = 2 * q := by omega
    rw [hcard, hpow q, smul_mul_assoc, one_mul]
    exact ⟨(-1 : ℤˣ) ^ ((m + 1) * q), by simp [toEvenBlade, hq]⟩
  · have hodd : Odd K.card := Nat.not_even_iff_odd.mp he
    rcases hodd with ⟨q, hq⟩
    rw [hq, pow_succ, mul_assoc]
    rcases ωOdd_mul_cBlade_eq_signed_compl R m K with ⟨s₁, hs₁⟩
    rw [hs₁, hpow q, smul_mul_assoc, one_mul, smul_smul]
    refine ⟨(-1 : ℤˣ) ^ ((m + 1) * q) * s₁, ?_⟩
    simp [toEvenBlade, he, Units.val_mul, Int.cast_mul]

theorem kBlade_mul_kBlade_eq_signed_symmDiff (R : Type*) [CommRing R] (m : ℕ)
    (K₁ K₂ : Finset (Fin (2 * m + 1))) :
    ∃ s : ℤˣ, kBlade R m K₁ * kBlade R m K₂ = ((s : ℤ) : R) • kBlade R m (symmDiff K₁ K₂) := by
  have hsq : ∀ r : Fin (2 * m + 1),
      kUnit R m r * kUnit R m r = ((((-1 : ℤˣ) ^ m : ℤˣ) : ℤ) : R) • (1 : CliffordAlgebra _) := by
    intro r
    rw [kUnit_sq R m r]
    simp
  simpa [kBlade, bladeList_toFinset] using
    listProd_mul_signed_symmDiff (2 * m + 1) (kUnit R m) ((-1 : ℤˣ) ^ m) hsq
      (fun {r s} hrs => kUnit_anticomm R m hrs) K₂ (bladeList K₁) (bladeList_nodup K₁)

end KBladesAndAllMQuaternionFactorization

section GeneralOddQuaternionFactorization

/-- Even-factor `p`-index pool `pPool r = {0, 1} ∪ {5, 6, ..., 4r+1, 4r+2}` (`p. 357`). -/
def pPool : ℕ → Finset ℕ
  | 0 => {0, 1}
  | r + 1 => pPool r ∪ {4 * r + 5, 4 * r + 6}

/-- Odd-factor `q`-index pool `qPool r = {2, 3, 4} ∪ {7, 8, ..., 4r+3, 4r+4}` (`p. 357`). -/
def qPool : ℕ → Finset ℕ
  | 0 => {2, 3, 4}
  | r + 1 => qPool r ∪ {4 * r + 7, 4 * r + 8}

/-- Predicate distinguishing `P`-lane (`{0,1, 5,6, 9,10,...}`) from `Q`-lane indices (`p. 357`). -/
def inPLane (x : ℕ) : Prop :=
  x < 2 ∨ (5 ≤ x ∧ (x - 5) % 4 < 2)

instance : DecidablePred inPLane := fun x =>
  inferInstanceAs (Decidable (x < 2 ∨ (5 ≤ x ∧ (x - 5) % 4 < 2)))

private lemma pPool_spec :
    ∀ r : ℕ, (∀ x ∈ pPool r, inPLane x ∧ x ≤ 4 * r + 2) ∧ (pPool r).card = 2 * (r + 1)
  | 0 => by
      refine ⟨?_, by decide⟩
      intro x hx
      simp only [pPool, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> refine ⟨Or.inl (by omega), by omega⟩
  | r + 1 => by
      have ih := pPool_spec r
      have h5 : 4 * r + 5 ∉ pPool r := fun h => by have := (ih.1 _ h).2; omega
      have h6 : 4 * r + 6 ∉ pPool r := fun h => by have := (ih.1 _ h).2; omega
      have h56 : (4 * r + 5 : ℕ) ≠ 4 * r + 6 := by omega
      have hdisj : Disjoint (pPool r) ({4 * r + 5, 4 * r + 6} : Finset ℕ) := by
        rw [Finset.disjoint_right]
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> assumption
      refine ⟨?_, ?_⟩
      · intro x hx
        simp only [pPool, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with hx' | rfl | rfl
        · have hx0 := ih.1 x hx'
          exact ⟨hx0.1, by omega⟩
        · refine ⟨Or.inr ⟨by omega, ?_⟩, by omega⟩
          have heq : 4 * r + 5 - 5 = 4 * r := by omega
          rw [heq, Nat.mul_mod_right]; decide
        · refine ⟨Or.inr ⟨by omega, ?_⟩, by omega⟩
          have heq : 4 * r + 6 - 5 = 4 * r + 1 := by omega
          rw [heq, Nat.add_mod, Nat.mul_mod_right]; decide
      · simp only [pPool]
        rw [Finset.card_union_of_disjoint hdisj, ih.2, Finset.card_pair h56]
        ring

private lemma qPool_spec :
    ∀ r : ℕ, (∀ x ∈ qPool r, ¬ inPLane x ∧ x ≤ 4 * r + 4) ∧ (qPool r).card = 2 * r + 3
  | 0 => by
      refine ⟨?_, by decide⟩
      intro x hx
      simp only [qPool, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> exact ⟨by decide, by omega⟩
  | r + 1 => by
      have ih := qPool_spec r
      have h7 : 4 * r + 7 ∉ qPool r := fun h => by have := (ih.1 _ h).2; omega
      have h8 : 4 * r + 8 ∉ qPool r := fun h => by have := (ih.1 _ h).2; omega
      have h78 : (4 * r + 7 : ℕ) ≠ 4 * r + 8 := by omega
      have hdisj : Disjoint (qPool r) ({4 * r + 7, 4 * r + 8} : Finset ℕ) := by
        rw [Finset.disjoint_right]
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> assumption
      refine ⟨?_, ?_⟩
      · intro x hx
        simp only [qPool, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with hx' | rfl | rfl
        · have hx0 := ih.1 x hx'
          exact ⟨hx0.1, by omega⟩
        · refine ⟨?_, by omega⟩
          rintro (hlt | ⟨_, hmod⟩)
          · omega
          · have heq : 4 * r + 7 - 5 = 4 * r + 2 := by omega
            rw [heq, Nat.add_mod, Nat.mul_mod_right] at hmod
            omega
        · refine ⟨?_, by omega⟩
          rintro (hlt | ⟨_, hmod⟩)
          · omega
          · have heq : 4 * r + 8 - 5 = 4 * r + 3 := by omega
            rw [heq, Nat.add_mod, Nat.mul_mod_right] at hmod
            omega
      · simp only [qPool]
        rw [Finset.card_union_of_disjoint hdisj, ih.2, Finset.card_pair h78]
        ring

private lemma pPool_mono {r₁ r₂ : ℕ} (h : r₁ ≤ r₂) : pPool r₁ ⊆ pPool r₂ := by
  induction h with
  | refl => exact Finset.Subset.rfl
  | step _ ih => exact ih.trans (Finset.subset_union_left)

private lemma qPool_mono {r₁ r₂ : ℕ} (h : r₁ ≤ r₂) : qPool r₁ ⊆ qPool r₂ := by
  induction h with
  | refl => exact Finset.Subset.rfl
  | step _ ih => exact ih.trans (Finset.subset_union_left)

/-- First `Nat`-valued factor generator index set `genSet1Nat j` (`p. 357`). -/
def genSet1Nat : ℕ → Finset ℕ
  | 0 => {0}
  | 1 => {3, 4}
  | j + 2 =>
      let k := j / 2
      if j % 2 = 0 then insert (4 * k + 5) (pPool k)
      else insert (4 * k + 7) (qPool k)

/-- Second `Nat`-valued factor generator index set `genSet2Nat j` (`p. 357`). -/
def genSet2Nat : ℕ → Finset ℕ
  | 0 => {1}
  | 1 => {2, 4}
  | j + 2 =>
      let k := j / 2
      if j % 2 = 0 then insert (4 * k + 6) (pPool k)
      else insert (4 * k + 8) (qPool k)

/-- `Nat`-to-`Fin n` set lift. -/
def finSetOfNat (n : ℕ) (S : Finset ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun x : Fin n => x.val ∈ S)

private lemma mem_finSetOfNat {n : ℕ} {S : Finset ℕ} {x : Fin n} :
    x ∈ finSetOfNat n S ↔ x.val ∈ S := by
  unfold finSetOfNat
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun hx => ⟨Finset.mem_univ x, hx⟩⟩

private lemma finSetOfNat_card {n : ℕ} (S : Finset ℕ) (hb : ∀ y ∈ S, y < n) :
    (finSetOfNat n S).card = S.card := by
  refine Finset.card_nbij (fun x => x.val) (fun x hx => mem_finSetOfNat.mp hx)
    (fun a _ b _ h => Fin.ext h) ?_
  intro y hy
  exact ⟨⟨y, hb y hy⟩, mem_finSetOfNat.mpr hy, rfl⟩

private lemma finSetOfNat_inter {n : ℕ} (S T : Finset ℕ) :
    finSetOfNat n (S ∩ T) = finSetOfNat n S ∩ finSetOfNat n T := by
  ext x; simp [finSetOfNat]

private lemma finSetOfNat_symmDiff {n : ℕ} (S T : Finset ℕ) :
    finSetOfNat n (symmDiff S T) = symmDiff (finSetOfNat n S) (finSetOfNat n T) := by
  ext x; simp [finSetOfNat, Finset.mem_symmDiff]

private lemma finSetOfNat_mono {n : ℕ} {S T : Finset ℕ} (h : S ⊆ T) :
    finSetOfNat n S ⊆ finSetOfNat n T := by
  intro x hx; exact mem_finSetOfNat.mpr (h (mem_finSetOfNat.mp hx))

private lemma finSetOfNat_inj {n : ℕ} {S T : Finset ℕ}
    (hS : ∀ y ∈ S, y < n) (hT : ∀ y ∈ T, y < n) (heq : finSetOfNat n S = finSetOfNat n T) :
    S = T := by
  ext y
  constructor
  · intro hy
    have hlt := hS y hy
    have hmem : (⟨y, hlt⟩ : Fin n) ∈ finSetOfNat n S := mem_finSetOfNat.mpr hy
    rw [heq] at hmem
    exact mem_finSetOfNat.mp hmem
  · intro hy
    have hlt := hT y hy
    have hmem : (⟨y, hlt⟩ : Fin n) ∈ finSetOfNat n T := mem_finSetOfNat.mpr hy
    rw [← heq] at hmem
    exact mem_finSetOfNat.mp hmem

private lemma genSet_lt_bound {m j : ℕ} (hj : j < m) :
    (∀ y ∈ genSet1Nat j, y < 2 * m + 1) ∧ (∀ y ∈ genSet2Nat j, y < 2 * m + 1) := by
  have hj_le : 2 * (j + 1) + 1 ≤ 2 * m + 1 := Nat.succ_le_succ (Nat.mul_le_mul_left 2 hj)
  rcases j with _ | _ | j'
  · refine ⟨?_, ?_⟩ <;> intro y hy <;> simp [genSet1Nat, genSet2Nat] at hy <;> omega
  · refine ⟨?_, ?_⟩ <;> intro y hy <;> simp [genSet1Nat, genSet2Nat] at hy <;> omega
  · simp only [genSet1Nat, genSet2Nat]
    split_ifs with hmod
    · have hk : j' = 2 * (j' / 2) := by omega
      have hbound : 4 * (j' / 2) + 6 < 2 * m + 1 := by omega
      refine ⟨?_, ?_⟩ <;> intro y hy <;> simp only [Finset.mem_insert] at hy
      · rcases hy with rfl | hyp
        · omega
        · have := (pPool_spec (j' / 2)).1 y hyp; omega
      · rcases hy with rfl | hyp
        · omega
        · have := (pPool_spec (j' / 2)).1 y hyp; omega
    · have hk : j' = 2 * (j' / 2) + 1 := by omega
      have hbound : 4 * (j' / 2) + 8 < 2 * m + 1 := by omega
      refine ⟨?_, ?_⟩ <;> intro y hy <;> simp only [Finset.mem_insert] at hy
      · rcases hy with rfl | hyq
        · omega
        · have := (qPool_spec (j' / 2)).1 y hyq; omega
      · rcases hy with rfl | hyq
        · omega
        · have := (qPool_spec (j' / 2)).1 y hyq; omega

/-- First generator `k`-blade support of the `j`-th quaternion factor (`j : Fin m`, `p. 357`). -/
def genKSet1 (m : ℕ) (j : Fin m) : Finset (Fin (2 * m + 1)) :=
  finSetOfNat (2 * m + 1) (genSet1Nat j.val)

/-- Second generator `k`-blade support of the `j`-th quaternion factor (`j : Fin m`, `p. 357`). -/
def genKSet2 (m : ℕ) (j : Fin m) : Finset (Fin (2 * m + 1)) :=
  finSetOfNat (2 * m + 1) (genSet2Nat j.val)

private lemma genSet_lane_card_inter (j : ℕ) :
    (genSet1Nat j).card = (genSet2Nat j).card ∧
      Odd ((genSet1Nat j).card * (genSet2Nat j).card + (genSet1Nat j ∩ genSet2Nat j).card) ∧
      (j % 2 = 0 →
        ((∀ y ∈ genSet1Nat j, inPLane y) ∧ (∀ y ∈ genSet2Nat j, inPLane y)) ∧
        Odd (genSet1Nat j).card ∧
        genSet1Nat j ⊆ pPool (j / 2) ∧ genSet2Nat j ⊆ pPool (j / 2)) ∧
      (j % 2 = 1 →
        ((∀ y ∈ genSet1Nat j, ¬ inPLane y) ∧ (∀ y ∈ genSet2Nat j, ¬ inPLane y)) ∧
        Even (genSet1Nat j).card ∧
        genSet1Nat j ⊆ qPool (j / 2) ∧ genSet2Nat j ⊆ qPool (j / 2)) ∧
      (∀ k : ℕ, j = 2 * k + 2 →
        pPool k ⊆ genSet1Nat j ∧ pPool k ⊆ genSet2Nat j) ∧
      (∀ k : ℕ, j = 2 * k + 3 →
        qPool k ⊆ genSet1Nat j ∧ qPool k ⊆ genSet2Nat j) := by
  rcases j with _ | _ | j'
  · refine ⟨by decide, by decide, ?_, ?_, ?_, ?_⟩
    · intro _; refine ⟨⟨?_, ?_⟩, by decide, ?_, ?_⟩
      · intro y hy; simp [genSet1Nat] at hy; subst hy; exact Or.inl (by decide)
      · intro y hy; simp [genSet2Nat] at hy; subst hy; exact Or.inl (by decide)
      · intro y hy; simp [genSet1Nat, pPool] at hy ⊢; omega
      · intro y hy; simp [genSet2Nat, pPool] at hy ⊢; omega
    · intro h; simp at h
    · intro k hk; omega
    · intro k hk; omega
  · refine ⟨by decide, by decide, ?_, ?_, ?_, ?_⟩
    · intro h; simp at h
    · intro _; refine ⟨⟨?_, ?_⟩, by decide, ?_, ?_⟩
      · intro y hy; simp [genSet1Nat] at hy; rcases hy with rfl | rfl <;> decide
      · intro y hy; simp [genSet2Nat] at hy; rcases hy with rfl | rfl <;> decide
      · intro y hy; simp [genSet1Nat, qPool] at hy ⊢; tauto
      · intro y hy; simp [genSet2Nat, qPool] at hy ⊢; tauto
    · intro k hk; omega
    · intro k hk; omega
  · have hps := pPool_spec (j' / 2)
    have hqs := qPool_spec (j' / 2)
    by_cases hmod : j' % 2 = 0
    · have h5not : 4 * (j' / 2) + 5 ∉ pPool (j' / 2) := fun h => by have := (hps.1 _ h).2; omega
      have h6not : 4 * (j' / 2) + 6 ∉ pPool (j' / 2) := fun h => by have := (hps.1 _ h).2; omega
      have hc1 : (genSet1Nat (j' + 2)).card = 2 * (j' / 2) + 3 := by
        simp [genSet1Nat, hmod, Finset.card_insert_of_notMem h5not, hps.2]; ring
      have hc2 : (genSet2Nat (j' + 2)).card = 2 * (j' / 2) + 3 := by
        simp [genSet2Nat, hmod, Finset.card_insert_of_notMem h6not, hps.2]; ring
      have hinter : genSet1Nat (j' + 2) ∩ genSet2Nat (j' + 2) = pPool (j' / 2) := by
        ext x
        simp only [genSet1Nat, genSet2Nat, hmod, ↓reduceIte, Finset.mem_inter, Finset.mem_insert]
        constructor
        · rintro ⟨rfl | hxp, h2⟩
          · rcases h2 with h56 | hx'
            · omega
            · exact False.elim (h5not hx')
          · exact hxp
        · intro hx; exact ⟨Or.inr hx, Or.inr hx⟩
      have hjmod : (j' + 2) % 2 = 0 := by omega
      have hjdiv : (j' + 2) / 2 = j' / 2 + 1 := by omega
      refine ⟨by rw [hc1, hc2], ?_, ?_, ?_, ?_, ?_⟩
      · rw [hc1, hc2, hinter, hps.2]
        refine ⟨2 * (j' / 2) ^ 2 + 7 * (j' / 2) + 5, by ring⟩
      · intro _
        refine ⟨⟨?_, ?_⟩, ⟨j' / 2 + 1, by rw [hc1]; ring⟩, ?_, ?_⟩
        · intro y hy
          simp only [genSet1Nat, hmod, ↓reduceIte, Finset.mem_insert] at hy
          rcases hy with rfl | hyp
          · refine Or.inr ⟨by omega, ?_⟩
            have he : 4 * (j' / 2) + 5 - 5 = 4 * (j' / 2) := by omega
            rw [he, Nat.mul_mod_right]; decide
          · exact (hps.1 y hyp).1
        · intro y hy
          simp only [genSet2Nat, hmod, ↓reduceIte, Finset.mem_insert] at hy
          rcases hy with rfl | hyp
          · refine Or.inr ⟨by omega, ?_⟩
            have he : 4 * (j' / 2) + 6 - 5 = 4 * (j' / 2) + 1 := by omega
            rw [he, Nat.add_mod, Nat.mul_mod_right]; decide
          · exact (hps.1 y hyp).1
        · rw [hjdiv]
          intro y hy
          simp only [genSet1Nat, hmod, ↓reduceIte, Finset.mem_insert] at hy
          simp only [pPool, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
          rcases hy with rfl | hyp
          · exact Or.inr (Or.inl rfl)
          · exact Or.inl hyp
        · rw [hjdiv]
          intro y hy
          simp only [genSet2Nat, hmod, ↓reduceIte, Finset.mem_insert] at hy
          simp only [pPool, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
          rcases hy with rfl | hyp
          · exact Or.inr (Or.inr rfl)
          · exact Or.inl hyp
      · intro h; omega
      · intro k hk
        have hkj : k = j' / 2 := by omega
        subst hkj
        simp only [genSet1Nat, genSet2Nat, hmod, ↓reduceIte]
        exact ⟨Finset.subset_insert _ _, Finset.subset_insert _ _⟩
      · intro k hk; omega
    · have hmod1 : j' % 2 = 1 := by omega
      have h7not : 4 * (j' / 2) + 7 ∉ qPool (j' / 2) := fun h => by have := (hqs.1 _ h).2; omega
      have h8not : 4 * (j' / 2) + 8 ∉ qPool (j' / 2) := fun h => by have := (hqs.1 _ h).2; omega
      have hif : (j' % 2 = 0) ↔ False := by simp [hmod1]
      have hc1 : (genSet1Nat (j' + 2)).card = 2 * (j' / 2) + 4 := by
        simp [genSet1Nat, hif, Finset.card_insert_of_notMem h7not, hqs.2]
      have hc2 : (genSet2Nat (j' + 2)).card = 2 * (j' / 2) + 4 := by
        simp [genSet2Nat, hif, Finset.card_insert_of_notMem h8not, hqs.2]
      have hinter : genSet1Nat (j' + 2) ∩ genSet2Nat (j' + 2) = qPool (j' / 2) := by
        ext x
        simp only [genSet1Nat, genSet2Nat, hif, ↓reduceIte, Finset.mem_inter, Finset.mem_insert]
        constructor
        · rintro ⟨rfl | hxq, h2⟩
          · rcases h2 with h78 | hx'
            · omega
            · exact False.elim (h7not hx')
          · exact hxq
        · intro hx; exact ⟨Or.inr hx, Or.inr hx⟩
      have hjmod : (j' + 2) % 2 = 1 := by omega
      have hjdiv : (j' + 2) / 2 = j' / 2 + 1 := by omega
      refine ⟨by rw [hc1, hc2], ?_, ?_, ?_, ?_, ?_⟩
      · rw [hc1, hc2, hinter, hqs.2]
        refine ⟨(2 * (j' / 2) + 4) * (j' / 2 + 2) + (j' / 2 + 1), by ring⟩
      · intro h; omega
      · intro _
        refine ⟨⟨?_, ?_⟩, ⟨j' / 2 + 2, by rw [hc1]; ring⟩, ?_, ?_⟩
        · intro y hy
          simp only [genSet1Nat, hif, ↓reduceIte, Finset.mem_insert] at hy
          rcases hy with rfl | hyq
          · rintro (hlt | ⟨_, hmod'⟩)
            · omega
            · have he : 4 * (j' / 2) + 7 - 5 = 4 * (j' / 2) + 2 := by omega
              rw [he, Nat.add_mod, Nat.mul_mod_right] at hmod'; omega
          · exact (hqs.1 y hyq).1
        · intro y hy
          simp only [genSet2Nat, hif, ↓reduceIte, Finset.mem_insert] at hy
          rcases hy with rfl | hyq
          · rintro (hlt | ⟨_, hmod'⟩)
            · omega
            · have he : 4 * (j' / 2) + 8 - 5 = 4 * (j' / 2) + 3 := by omega
              rw [he, Nat.add_mod, Nat.mul_mod_right] at hmod'; omega
          · exact (hqs.1 y hyq).1
        · rw [hjdiv]
          intro y hy
          simp only [genSet1Nat, hif, ↓reduceIte, Finset.mem_insert] at hy
          simp only [qPool, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
          rcases hy with rfl | hyq
          · exact Or.inr (Or.inl rfl)
          · exact Or.inl hyq
        · rw [hjdiv]
          intro y hy
          simp only [genSet2Nat, hif, ↓reduceIte, Finset.mem_insert] at hy
          simp only [qPool, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
          rcases hy with rfl | hyq
          · exact Or.inr (Or.inr rfl)
          · exact Or.inl hyq
      · intro k hk; omega
      · intro k hk
        have hkj : k = j' / 2 := by omega
        subst hkj
        simp only [genSet1Nat, genSet2Nat, hif, ↓reduceIte]
        exact ⟨Finset.subset_insert _ _, Finset.subset_insert _ _⟩

/-- Square scalar coefficient `cFactor R m j ∈ {-1, +1}` of the `j`-th quaternion factor
(`j : Fin m`) inside `Cl⁰(0, 2m+1)` (`p. 357`). -/
def cFactor (R : Type*) [CommRing R] (m : ℕ) (j : Fin m) : R :=
  (-1 : R) ^ (m * (genKSet1 m j).card + (genKSet1 m j).card * ((genKSet1 m j).card - 1) / 2)

theorem cFactor_zero (R : Type*) [CommRing R] {m : ℕ} (hm : 1 ≤ m) :
    cFactor R m ⟨0, hm⟩ = (-1 : R) ^ m := by
  have hlt := (genSet_lt_bound (m := m) (j := 0) hm).1
  have hc : (genKSet1 m ⟨0, hm⟩).card = 1 := by
    rw [genKSet1, finSetOfNat_card _ hlt]; decide
  simp [cFactor, hc]

theorem cFactor_one (R : Type*) [CommRing R] {m : ℕ} (hm : 2 ≤ m) :
    cFactor R m ⟨1, hm⟩ = -1 := by
  have hlt := (genSet_lt_bound (m := m) (j := 1) hm).1
  have hc : (genKSet1 m ⟨1, hm⟩).card = 2 := by
    rw [genKSet1, finSetOfNat_card _ hlt]; decide
  have hexp : m * 2 + 2 * (2 - 1) / 2 = 2 * m + 1 := by omega
  simp [cFactor, hc, hexp, pow_add, pow_mul]

/-- Explicit `QuaternionAlgebra.Basis` structure on the `j`-th commuting factor of `Cl⁰(0, 2m+1)`
for EVERY `m` and `j : Fin m` (`pp. 356–357`). -/
def factorQuatBasis (R : Type*) [CommRing R] (m : ℕ) (j : Fin m) :
    QuaternionAlgebra.Basis (CliffordAlgebra (cliffordNegSqForm R (2 * m + 1)))
      (cFactor R m j) 0 (cFactor R m j) where
  i := kBlade R m (genKSet1 m j)
  j := kBlade R m (genKSet2 m j)
  k := kBlade R m (genKSet1 m j) * kBlade R m (genKSet2 m j)
  i_mul_i := by
    rw [kBlade_sq, cFactor, zero_smul, add_zero]
  j_mul_j := by
    have hlt := genSet_lt_bound j.isLt
    have hcard : (genKSet2 m j).card = (genKSet1 m j).card := by
      simp only [genKSet1, genKSet2, finSetOfNat_card _ hlt.1, finSetOfNat_card _ hlt.2,
        (genSet_lane_card_inter j.val).1]
    rw [kBlade_sq, hcard, cFactor]
  i_mul_j := rfl
  j_mul_i := by
    have hlt := genSet_lt_bound j.isLt
    have hinter_lt : ∀ y ∈ genSet1Nat j.val ∩ genSet2Nat j.val, y < 2 * m + 1 :=
      fun y hy => hlt.1 y (Finset.inter_subset_left hy)
    have hodd : Odd ((genKSet1 m j).card * (genKSet2 m j).card +
        (genKSet1 m j ∩ genKSet2 m j).card) := by
      simp only [genKSet1, genKSet2, ← finSetOfNat_inter,
        finSetOfNat_card _ hlt.1, finSetOfNat_card _ hlt.2, finSetOfNat_card _ hinter_lt]
      exact (genSet_lane_card_inter j.val).2.1
    rw [zero_smul, zero_sub, kBlade_mul_swap R m (genKSet2 m j) (genKSet1 m j),
      mul_comm (genKSet2 m j).card, Finset.inter_comm]
    rcases hodd with ⟨q, hq⟩
    rw [hq, pow_add, pow_mul]
    simp

/-- The four quaternion basis elements `{1, i, j, k}` of factor `j : Fin m`. -/
def factorElem (R : Type*) [CommRing R] (m : ℕ) (j : Fin m) :
    Fin 4 → CliffordAlgebra (cliffordNegSqForm R (2 * m + 1))
  | 0 => 1
  | 1 => (factorQuatBasis R m j).i
  | 2 => (factorQuatBasis R m j).j
  | 3 => (factorQuatBasis R m j).k

theorem factorElem_mem_even (R : Type*) [CommRing R] (m : ℕ) (j : Fin m) (a : Fin 4) :
    factorElem R m j a ∈ CliffordAlgebra.even (cliffordNegSqForm R (2 * m + 1)) := by
  fin_cases a
  · exact Subalgebra.one_mem _
  · exact kBlade_mem_even R m (genKSet1 m j)
  · exact kBlade_mem_even R m (genKSet2 m j)
  · exact Subalgebra.mul_mem _ (kBlade_mem_even R m (genKSet1 m j))
      (kBlade_mem_even R m (genKSet2 m j))

private lemma genKSet_comm_aux (R : Type*) [CommRing R] (m : ℕ) {i j : Fin m} (hlt : i < j)
    (A B : Finset (Fin (2 * m + 1)))
    (hA : A = genKSet1 m i ∨ A = genKSet2 m i)
    (hB : B = genKSet1 m j ∨ B = genKSet2 m j) :
    Commute (kBlade R m A) (kBlade R m B) := by
  refine kBlade_commute_of_even R m ?_
  have hs_i := genSet_lane_card_inter i.val
  have hs_j := genSet_lane_card_inter j.val
  have hbi := genSet_lt_bound i.isLt
  have hbj := genSet_lt_bound j.isLt
  have hij_nat : i.val < j.val := hlt
  have hA_prop : ∃ SA : Finset ℕ, A = finSetOfNat (2 * m + 1) SA ∧
      (SA = genSet1Nat i.val ∨ SA = genSet2Nat i.val) ∧ (∀ y ∈ SA, y < 2 * m + 1) := by
    rcases hA with rfl | rfl
    · exact ⟨genSet1Nat i.val, rfl, Or.inl rfl, hbi.1⟩
    · exact ⟨genSet2Nat i.val, rfl, Or.inr rfl, hbi.2⟩
  have hB_prop : ∃ SB : Finset ℕ, B = finSetOfNat (2 * m + 1) SB ∧
      (SB = genSet1Nat j.val ∨ SB = genSet2Nat j.val) ∧ (∀ y ∈ SB, y < 2 * m + 1) := by
    rcases hB with rfl | rfl
    · exact ⟨genSet1Nat j.val, rfl, Or.inl rfl, hbj.1⟩
    · exact ⟨genSet2Nat j.val, rfl, Or.inr rfl, hbj.2⟩
  rcases hA_prop with ⟨SA, rfl, hSA_eq, hSA_lt⟩
  rcases hB_prop with ⟨SB, rfl, hSB_eq, hSB_lt⟩
  have hinter_lt : ∀ y ∈ SA ∩ SB, y < 2 * m + 1 := fun y hy => hSA_lt y (Finset.inter_subset_left hy)
  rw [← finSetOfNat_inter, finSetOfNat_card _ hSA_lt, finSetOfNat_card _ hSB_lt,
    finSetOfNat_card _ hinter_lt]
  have hSA_card : SA.card = (genSet1Nat i.val).card := by
    rcases hSA_eq with rfl | rfl
    · rfl
    · exact hs_i.1.symm
  have hSB_card : SB.card = (genSet1Nat j.val).card := by
    rcases hSB_eq with rfl | rfl
    · rfl
    · exact hs_j.1.symm
  rcases Nat.mod_two_eq_zero_or_one i.val with hi0 | hi1 <;>
    rcases Nat.mod_two_eq_zero_or_one j.val with hj0 | hj1
  · -- Both even: SA ⊆ pPool (i/2) ⊆ pPool ((j-2)/2) ⊆ SB, both odd card
    have hj_ge : 2 ≤ j.val := by omega
    let k := (j.val - 2) / 2
    have hjk : j.val = 2 * k + 2 := by omega
    have hi_le : i.val / 2 ≤ k := by omega
    have hSA_sub_p : SA ⊆ pPool (i.val / 2) := by
      have hp := (hs_i.2.2.1 hi0).2.2
      rcases hSA_eq with rfl | rfl <;> [exact hp.1; exact hp.2]
    have hp_sub_SB : pPool k ⊆ SB := by
      have hp := hs_j.2.2.2.2.1 k hjk
      rcases hSB_eq with rfl | rfl <;> [exact hp.1; exact hp.2]
    have hsub : SA ⊆ SB := hSA_sub_p.trans ((pPool_mono hi_le).trans hp_sub_SB)
    rw [Finset.inter_eq_left.mpr hsub, hSA_card, hSB_card]
    rcases (hs_i.2.2.1 hi0).2.1 with ⟨a, ha⟩
    rcases (hs_j.2.2.1 hj0).2.1 with ⟨b, hb⟩
    rw [ha, hb]
    exact ⟨2 * a * b + a + b + a + 1, by ring⟩
  · -- i even (in P-lane), j odd (not in P-lane, even card)
    have hP : ∀ y ∈ SA, inPLane y := by
      have hp := (hs_i.2.2.1 hi0).1
      rcases hSA_eq with rfl | rfl <;> [exact hp.1; exact hp.2]
    have hQ : ∀ y ∈ SB, ¬ inPLane y := by
      have hq := (hs_j.2.2.2.1 hj1).1
      rcases hSB_eq with rfl | rfl <;> [exact hq.1; exact hq.2]
    have hinter0 : SA ∩ SB = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro y hy
      rw [Finset.mem_inter] at hy
      exact hQ y hy.2 (hP y hy.1)
    rw [hinter0, Finset.card_empty, add_zero, hSB_card]
    rcases (hs_j.2.2.2.1 hj1).2.1 with ⟨b, hb⟩
    rw [hb]
    exact ⟨SA.card * b, by ring⟩
  · -- i odd (not in P-lane, even card), j even (in P-lane)
    have hQ : ∀ y ∈ SA, ¬ inPLane y := by
      have hq := (hs_i.2.2.2.1 hi1).1
      rcases hSA_eq with rfl | rfl <;> [exact hq.1; exact hq.2]
    have hP : ∀ y ∈ SB, inPLane y := by
      have hp := (hs_j.2.2.1 hj0).1
      rcases hSB_eq with rfl | rfl <;> [exact hp.1; exact hp.2]
    have hinter0 : SA ∩ SB = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro y hy
      rw [Finset.mem_inter] at hy
      exact hQ y hy.1 (hP y hy.2)
    rw [hinter0, Finset.card_empty, add_zero, hSA_card]
    rcases (hs_i.2.2.2.1 hi1).2.1 with ⟨a, ha⟩
    rw [ha]
    exact ⟨a * SB.card, by ring⟩
  · -- Both odd: SA ⊆ qPool (i/2) ⊆ qPool ((j-2)/2) ⊆ SB, both even card
    have hj_ge : 3 ≤ j.val := by omega
    let k := (j.val - 2) / 2
    have hjk : j.val = 2 * k + 3 := by omega
    have hi_le : i.val / 2 ≤ k := by omega
    have hSA_sub_q : SA ⊆ qPool (i.val / 2) := by
      have hq := (hs_i.2.2.2.1 hi1).2.2
      rcases hSA_eq with rfl | rfl <;> [exact hq.1; exact hq.2]
    have hq_sub_SB : qPool k ⊆ SB := by
      have hq := hs_j.2.2.2.2.2 k hjk
      rcases hSB_eq with rfl | rfl <;> [exact hq.1; exact hq.2]
    have hsub : SA ⊆ SB := hSA_sub_q.trans ((qPool_mono hi_le).trans hq_sub_SB)
    rw [Finset.inter_eq_left.mpr hsub, hSA_card, hSB_card]
    rcases (hs_i.2.2.2.1 hi1).2.1 with ⟨a, ha⟩
    rcases (hs_j.2.2.2.1 hj1).2.1 with ⟨b, hb⟩
    rw [ha, hb]
    exact ⟨2 * a * b + a, by ring⟩

/-- **Clifford (1878, `p. 357`) Mutually Commuting Quaternion Factorization Theorem**:
distinct quaternion factors `i ≠ j` in `Cl⁰(0, 2m+1)` pairwise commute elementwise. -/
theorem factorElem_comm_of_ne (R : Type*) [CommRing R] (m : ℕ) {i j : Fin m}
    (hij : i ≠ j) (a b : Fin 4) :
    Commute (factorElem R m i a) (factorElem R m j b) := by
  have hgen : ∀ A B : Finset (Fin (2 * m + 1)),
      (A = genKSet1 m i ∨ A = genKSet2 m i) →
      (B = genKSet1 m j ∨ B = genKSet2 m j) →
      Commute (kBlade R m A) (kBlade R m B) := by
    intro A B hA hB
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact genKSet_comm_aux R m hlt A B hA hB
    · exact (genKSet_comm_aux R m hgt B A hB hA).symm
  have h1 : ∀ b : Fin 4,
      (Commute (kBlade R m (genKSet1 m i)) (factorElem R m j b)) ∧
      (Commute (kBlade R m (genKSet2 m i)) (factorElem R m j b)) := by
    intro b'
    fin_cases b'
    · exact ⟨Commute.one_right _, Commute.one_right _⟩
    · exact ⟨hgen _ _ (Or.inl rfl) (Or.inl rfl), hgen _ _ (Or.inr rfl) (Or.inl rfl)⟩
    · exact ⟨hgen _ _ (Or.inl rfl) (Or.inr rfl), hgen _ _ (Or.inr rfl) (Or.inr rfl)⟩
    · refine ⟨(hgen _ _ (Or.inl rfl) (Or.inl rfl)).mul_right
          (hgen _ _ (Or.inl rfl) (Or.inr rfl)),
        (hgen _ _ (Or.inr rfl) (Or.inl rfl)).mul_right
          (hgen _ _ (Or.inr rfl) (Or.inr rfl))⟩
  fin_cases a
  · exact Commute.one_left _
  · exact (h1 b).1
  · exact (h1 b).2
  · exact (h1 b).1.mul_left (h1 b).2

/-- `Nat` support set corresponding to factor `j` and quaternion slot `a ∈ {0, 1, 2, 3}`. -/
def factorKSetNat (j : ℕ) : Fin 4 → Finset ℕ
  | 0 => ∅
  | 1 => genSet1Nat j
  | 2 => genSet2Nat j
  | 3 => symmDiff (genSet1Nat j) (genSet2Nat j)

/-- `Fin (2m+1)` `k`-blade support corresponding to factor `j : Fin m` and slot `a : Fin 4`. -/
def factorKSet (m : ℕ) (j : Fin m) (a : Fin 4) : Finset (Fin (2 * m + 1)) :=
  finSetOfNat (2 * m + 1) (factorKSetNat j.val a)

/-- Composite `Nat`-valued `k`-blade support of tuple `t : Fin m → Fin 4`. -/
def tupleKSetNat (m : ℕ) (t : Fin m → Fin 4) : Finset ℕ :=
  ((List.finRange m).map (fun j => factorKSetNat j.val (t j))).foldr symmDiff ∅

/-- Composite `Fin (2m+1)` `k`-blade support of tuple `t : Fin m → Fin 4`. -/
def tupleKSet (m : ℕ) (t : Fin m → Fin 4) : Finset (Fin (2 * m + 1)) :=
  ((List.finRange m).map (fun j => factorKSet m j (t j))).foldr symmDiff ∅

/-- Exact product of the `m` commuting quaternion-factor choices `t : Fin m → Fin 4` (`p. 358`). -/
def factorProd (R : Type*) [CommRing R] (m : ℕ) (t : Fin m → Fin 4) :
    CliffordAlgebra (cliffordNegSqForm R (2 * m + 1)) :=
  ((List.finRange m).map (fun j => factorElem R m j (t j))).prod

theorem factorProd_eq_signed_evenBlade (R : Type*) [CommRing R] (m : ℕ) (t : Fin m → Fin 4) :
    ∃ s : ℤˣ, factorProd R m t =
      ((s : ℤ) : R) • cBlade R (2 * m + 1) (toEvenBlade m (tupleKSet m t)) := by
  have hfac : ∀ (j : Fin m) (a : Fin 4),
      ∃ s : ℤˣ, factorElem R m j a = ((s : ℤ) : R) • kBlade R m (factorKSet m j a) := by
    intro j a
    fin_cases a
    · exact ⟨1, by simp [factorElem, factorKSet, factorKSetNat, finSetOfNat]⟩
    · exact ⟨1, by simp [factorElem, factorQuatBasis, factorKSet, factorKSetNat, genKSet1]⟩
    · exact ⟨1, by simp [factorElem, factorQuatBasis, factorKSet, factorKSetNat, genKSet2]⟩
    · simpa [factorElem, factorQuatBasis, factorKSet, factorKSetNat, genKSet1, genKSet2,
        finSetOfNat_symmDiff] using
        kBlade_mul_kBlade_eq_signed_symmDiff R m (genKSet1 m j) (genKSet2 m j)
  have hlist : ∀ L : List (Fin m),
      ∃ s : ℤˣ, (L.map (fun j => factorElem R m j (t j))).prod =
        ((s : ℤ) : R) • kBlade R m ((L.map (fun j => factorKSet m j (t j))).foldr symmDiff ∅) := by
    intro L
    induction L with
    | nil => exact ⟨1, by simp⟩
    | cons hd tl ih =>
        rcases hfac hd (t hd) with ⟨s₁, hs₁⟩
        rcases ih with ⟨s₂, hs₂⟩
        rcases kBlade_mul_kBlade_eq_signed_symmDiff R m (factorKSet m hd (t hd))
          ((tl.map (fun j => factorKSet m j (t j))).foldr symmDiff ∅) with ⟨s₃, hs₃⟩
        refine ⟨s₁ * s₂ * s₃, ?_⟩
        calc
          ((hd :: tl).map (fun j => factorElem R m j (t j))).prod
              = factorElem R m hd (t hd) * (tl.map (fun j => factorElem R m j (t j))).prod := by
                simp
          _ = (((s₁ : ℤ) : R) • kBlade R m (factorKSet m hd (t hd))) *
                (((s₂ : ℤ) : R) • kBlade R m ((tl.map (fun j => factorKSet m j (t j))).foldr symmDiff ∅)) := by
                rw [hs₁, hs₂]
          _ = ((s₁ : ℤ) : R) • (((s₂ : ℤ) : R) •
                (kBlade R m (factorKSet m hd (t hd)) *
                  kBlade R m ((tl.map (fun j => factorKSet m j (t j))).foldr symmDiff ∅))) := by
                rw [smul_mul_assoc, mul_smul_comm]
          _ = (((s₁ * s₂ * s₃ : ℤˣ) : ℤ) : R) •
                kBlade R m (symmDiff (factorKSet m hd (t hd))
                  ((tl.map (fun j => factorKSet m j (t j))).foldr symmDiff ∅)) := by
                rw [hs₃, smul_smul, smul_smul, Units.val_mul, Units.val_mul, Int.cast_mul,
                  Int.cast_mul]
          _ = (((s₁ * s₂ * s₃ : ℤˣ) : ℤ) : R) •
                kBlade R m (((hd :: tl).map (fun j => factorKSet m j (t j))).foldr symmDiff ∅) := by
                simp [List.map_cons, List.foldr_cons]
  rcases hlist (List.finRange m) with ⟨s₁, hs₁⟩
  rcases kBlade_eq_signed_cBlade_toEvenBlade R m (tupleKSet m t) with ⟨s₂, hs₂⟩
  refine ⟨s₁ * s₂, ?_⟩
  calc
    factorProd R m t = ((s₁ : ℤ) : R) • kBlade R m (tupleKSet m t) := hs₁
    _ = ((s₁ : ℤ) : R) • (((s₂ : ℤ) : R) • cBlade R (2 * m + 1) (toEvenBlade m (tupleKSet m t))) := by
        rw [hs₂]
    _ = (((s₁ * s₂ : ℤˣ) : ℤ) : R) • cBlade R (2 * m + 1) (toEvenBlade m (tupleKSet m t)) := by
        rw [smul_smul, Units.val_mul, Int.cast_mul]

/-- Map sending each `m`-tuple `t : Fin m → Fin 4` of factor choices to its even basis blade
support inside `Cl⁰(0, 2m+1)`. -/
def evenSupportOfTuple (m : ℕ) (t : Fin m → Fin 4) :
    {S : Finset (Fin (2 * m + 1)) // Even S.card} :=
  ⟨toEvenBlade m (tupleKSet m t), toEvenBlade_card_even m (tupleKSet m t)⟩

private def evenFinsetEquiv (n : ℕ) :
    Finset (Fin n) ≃ {S : Finset (Fin (n + 1)) // Even S.card} where
  toFun T :=
    if h : Even T.card then ⟨T.map Fin.castSuccEmb, by simpa⟩
    else ⟨insert (Fin.last n) (T.map Fin.castSuccEmb), by
      have hnot : Fin.last n ∉ T.map Fin.castSuccEmb := by
        simp only [Finset.mem_map, Fin.castSuccEmb_apply, not_exists, not_and]
        intro x _; exact Fin.castSucc_lt_last x |>.ne
      rw [Finset.card_insert_of_notMem hnot, Finset.card_map]
      rcases Nat.not_even_iff_odd.mp h with ⟨k, hk⟩
      exact ⟨k + 1, by omega⟩⟩
  invFun S := Finset.univ.filter (fun x : Fin n => x.castSucc ∈ S.1)
  left_inv T := by
    ext x
    dsimp only
    split_ifs <;> simp [Fin.castSucc_inj]
  right_inv S := by
    rcases S with ⟨S, hS⟩
    ext1
    dsimp only
    let T := Finset.univ.filter (fun x : Fin n => x.castSucc ∈ S)
    have hmap : T.map Fin.castSuccEmb = S.erase (Fin.last n) := by
      ext y
      simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
        Fin.castSuccEmb_apply, Finset.mem_erase, T]
      constructor
      · rintro ⟨x, hxS, rfl⟩
        exact ⟨Fin.castSucc_lt_last x |>.ne, hxS⟩
      · rintro ⟨hne, hyS⟩
        have hlt : y.val < n := by
          have := y.isLt
          have hne_val : y.val ≠ n := fun h => hne (Fin.ext h)
          omega
        exact ⟨⟨y.val, hlt⟩, by simpa [Fin.castSucc_mk], Fin.ext rfl⟩
    have hcardT : T.card = (S.erase (Fin.last n)).card := by
      rw [← Finset.card_map Fin.castSuccEmb, hmap]
    split_ifs with he
    · change Finset.map Fin.castSuccEmb T = S
      rw [hmap]
      by_cases hlast : Fin.last n ∈ S
      · rw [Finset.card_erase_of_mem hlast] at hcardT
        rw [hcardT] at he
        rcases hS with ⟨a, ha⟩
        rcases he with ⟨b, hb⟩
        have hpos : 0 < S.card := Finset.card_pos.mpr ⟨Fin.last n, hlast⟩
        omega
      · exact Finset.erase_eq_of_notMem hlast
    · change insert (Fin.last n) (Finset.map Fin.castSuccEmb T) = S
      rw [hmap]
      by_cases hlast : Fin.last n ∈ S
      · exact Finset.insert_erase hlast
      · rw [Finset.erase_eq_of_notMem hlast] at hcardT
        exact False.elim (he (hcardT ▸ hS))

private lemma card_evenFinset_subtype (n : ℕ) :
    Fintype.card {S : Finset (Fin (n + 1)) // Even S.card} = 2 ^ n := by
  rw [← Fintype.card_congr (evenFinsetEquiv n), Fintype.card_finset, Fintype.card_fin]

private lemma mem_foldr_symmDiff_iff {α : Type*} [DecidableEq α] (x : α) :
    ∀ L : List (Finset α),
      x ∈ L.foldr symmDiff ∅ ↔ Odd (L.countP (fun S => decide (x ∈ S)))
  | [] => by simp
  | S :: tl => by
      have ih := mem_foldr_symmDiff_iff x tl
      simp only [List.foldr_cons, Finset.mem_symmDiff, List.countP_cons, ih]
      by_cases hxS : x ∈ S
      · simp [hxS, Nat.odd_iff]; omega
      · simp [hxS]

private lemma countP_finRange_eq_sum (m : ℕ) (p : Fin m → Bool) :
    (List.finRange m).countP p = ∑ j : Fin m, if p j then 1 else 0 := by
  induction m with
  | zero => simp
  | succ k ih =>
      rw [List.finRange_succ, List.countP_cons, List.countP_map, Fin.sum_univ_succ]
      have hid := ih (fun j : Fin k => p j.succ)
      have hcomp : p ∘ Fin.succ = fun j : Fin k => p j.succ := rfl
      rw [hcomp, hid]
      by_cases hp : p 0 = true <;> simp [hp, add_comm]

private lemma mem_tupleKSetNat_iff (m : ℕ) (t : Fin m → Fin 4) (y : ℕ) :
    y ∈ tupleKSetNat m t ↔
      Odd (∑ j : Fin m, if y ∈ factorKSetNat j.val (t j) then 1 else 0) := by
  simp only [tupleKSetNat, mem_foldr_symmDiff_iff, List.countP_map]
  have hcomp : (fun S => decide (y ∈ S)) ∘ (fun j : Fin m => factorKSetNat j.val (t j)) =
      fun j : Fin m => decide (y ∈ factorKSetNat j.val (t j)) := rfl
  rw [hcomp, countP_finRange_eq_sum]
  simp only [decide_eq_true_eq]

private lemma tupleKSet_eq_finSetOfNat (m : ℕ) (t : Fin m → Fin 4) :
    tupleKSet m t = finSetOfNat (2 * m + 1) (tupleKSetNat m t) := by
  have hL : ∀ L : List (Fin m),
      (L.map (fun j => factorKSet m j (t j))).foldr symmDiff ∅ =
        finSetOfNat (2 * m + 1) ((L.map (fun j => factorKSetNat j.val (t j))).foldr symmDiff ∅) := by
    intro L
    induction L with
    | nil => simp [finSetOfNat]
    | cons a tl ih =>
        rw [List.map_cons, List.foldr_cons, ih, factorKSet, ← finSetOfNat_symmDiff]
        rfl
  simpa [tupleKSet, tupleKSetNat] using hL (List.finRange m)

private lemma factorKSetNat_lt_bound (m : ℕ) (j : Fin m) (a : Fin 4)
    {y : ℕ} (hy : y ∈ factorKSetNat j.val a) : y < 2 * m + 1 := by
  have hlt := genSet_lt_bound j.isLt
  fin_cases a
  · simp [factorKSetNat] at hy
  · exact hlt.1 y hy
  · exact hlt.2 y hy
  · simp only [factorKSetNat, Finset.mem_symmDiff] at hy
    rcases hy with ⟨h, _⟩ | ⟨h, _⟩ <;> [exact hlt.1 y h; exact hlt.2 y h]

private lemma tupleKSetNat_lt_bound (m : ℕ) (t : Fin m → Fin 4)
    {y : ℕ} (hy : y ∈ tupleKSetNat m t) : y < 2 * m + 1 := by
  rw [mem_tupleKSetNat_iff] at hy
  by_contra hge
  have hzero : ∀ j : Fin m, y ∉ factorKSetNat j.val (t j) := fun j hj =>
    hge (factorKSetNat_lt_bound m j (t j) hj)
  have hsum0 : (∑ j : Fin m, if y ∈ factorKSetNat j.val (t j) then 1 else 0) = 0 :=
    Finset.sum_eq_zero fun j _ => by simp [hzero j]
  rw [hsum0] at hy
  exact Nat.not_odd_zero hy

private lemma symmDiff_even_card {α : Type*} [DecidableEq α] {A B : Finset α}
    (hA : Even A.card) (hB : Even B.card) : Even (symmDiff A B).card := by
  have hdisj : Disjoint (A \ B) (B \ A) :=
    Finset.disjoint_left.mpr fun _ hx1 hx2 =>
      (Finset.mem_sdiff.mp hx2).2 (Finset.mem_sdiff.mp hx1).1
  have hsd : symmDiff A B = (A \ B) ∪ (B \ A) := rfl
  rw [hsd, Finset.card_union_of_disjoint hdisj]
  have ha1 : (A \ B).card + (A ∩ B).card = A.card := Finset.card_sdiff_add_card_inter A B
  have hb1 : (B \ A).card + (A ∩ B).card = B.card := by
    rw [Finset.inter_comm]; exact Finset.card_sdiff_add_card_inter B A
  rcases hA with ⟨a, ha⟩
  rcases hB with ⟨b, hb⟩
  exact ⟨a + b - (A ∩ B).card, by omega⟩

/-- `Q`-lane index subset inside `Fin (2m+1)`, invariant under `kBlade → cBlade` polarity parity. -/
def qLaneSet (m : ℕ) : Finset (Fin (2 * m + 1)) :=
  Finset.univ.filter (fun x => ¬ inPLane x.val)

private lemma qLaneSet_card_odd : ∀ {m : ℕ}, 1 ≤ m → Odd (qLaneSet m).card
  | 0, hm => by omega
  | 1, _ => by
      have hq : qLaneSet 1 = {2} := by decide
      rw [hq]; exact ⟨0, by simp⟩
  | k + 2, _ => by
      have ih := qLaneSet_card_odd (m := k + 1) (by omega)
      let castEmb : Fin (2 * (k + 1) + 1) ↪ Fin (2 * (k + 2) + 1) := Fin.castLEEmb (by omega)
      let x1 : Fin (2 * (k + 2) + 1) := ⟨2 * k + 3, by omega⟩
      let x2 : Fin (2 * (k + 2) + 1) := ⟨2 * k + 4, by omega⟩
      have hpart : qLaneSet (k + 2) =
          (qLaneSet (k + 1)).map castEmb ∪
            (({x1, x2} : Finset (Fin (2 * (k + 2) + 1))).filter (fun x => ¬ inPLane x.val)) := by
        ext z
        simp only [qLaneSet, Finset.mem_union, Finset.mem_map, Finset.mem_filter, Finset.mem_univ,
          true_and, Finset.mem_insert, Finset.mem_singleton, x1, x2]
        constructor
        · intro hz
          by_cases hlt : z.val < 2 * (k + 1) + 1
          · exact Or.inl ⟨⟨z.val, hlt⟩, hz, Fin.ext rfl⟩
          · refine Or.inr ⟨?_, hz⟩
            have hle : z.val < 2 * (k + 2) + 1 := z.isLt
            by_cases hz3 : z.val = 2 * k + 3
            · exact Or.inl (Fin.ext hz3)
            · exact Or.inr (Fin.ext (show z.val = 2 * k + 4 by omega))
        · rintro (⟨w, hw, rfl⟩ | ⟨(rfl | rfl), hz⟩)
          · exact hw
          · exact hz
          · exact hz
      have hdisj : Disjoint ((qLaneSet (k + 1)).map castEmb)
          (({x1, x2} : Finset (Fin (2 * (k + 2) + 1))).filter (fun x => ¬ inPLane x.val)) := by
        rw [Finset.disjoint_left]
        rintro z hz1 hz2
        simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_insert,
          Finset.mem_singleton, qLaneSet, x1, x2] at hz1 hz2
        rcases hz1 with ⟨w, _, rfl⟩
        have hwlt := w.isLt
        rcases hz2.1 with h | h
        · have hv : w.val = 2 * k + 3 := congrArg Fin.val h
          omega
        · have hv : w.val = 2 * k + 4 := congrArg Fin.val h
          omega
      have hpair_even :
          Even (({x1, x2} : Finset (Fin (2 * (k + 2) + 1))).filter
            (fun x => ¬ inPLane x.val)).card := by
        have h12 : ¬ inPLane x1.val ↔ ¬ inPLane x2.val := by
          simp only [x1, x2, inPLane]
          omega
        by_cases hp : ¬ inPLane x1.val
        · have hp2 : ¬ inPLane x2.val := h12.mp hp
          have heq : (({x1, x2} : Finset (Fin (2 * (k + 2) + 1))).filter
              (fun x => ¬ inPLane x.val)) = {x1, x2} := by
            ext z; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
            constructor
            · exact And.left
            · rintro (rfl | rfl); exact ⟨Or.inl rfl, hp⟩; exact ⟨Or.inr rfl, hp2⟩
          have hne : x1 ≠ x2 := fun h => by
            have hv := congrArg Fin.val h; simp [x1, x2] at hv
          rw [heq, Finset.card_pair hne]
          exact ⟨1, rfl⟩
        · have hp2 : ¬ ¬ inPLane x2.val := mt h12.mpr hp
          have heq : (({x1, x2} : Finset (Fin (2 * (k + 2) + 1))).filter
              (fun x => ¬ inPLane x.val)) = ∅ := by
            rw [Finset.eq_empty_iff_forall_notMem]
            intro z hz
            simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] at hz
            rcases hz.1 with rfl | rfl
            · exact hp hz.2
            · exact hp2 hz.2
          rw [heq, Finset.card_empty]
          exact ⟨0, rfl⟩
      rw [hpart, Finset.card_union_of_disjoint hdisj, Finset.card_map]
      exact ih.add_even hpair_even

private lemma tupleKSet_inter_qLaneSet_even (m : ℕ) (t : Fin m → Fin 4) :
    Even ((tupleKSet m t ∩ qLaneSet m).card) := by
  have hfac : ∀ (j : Fin m) (a : Fin 4), Even ((factorKSet m j a ∩ qLaneSet m).card) := by
    intro j a
    have hspec := genSet_lane_card_inter j.val
    have hlt := genSet_lt_bound j.isLt
    rcases Nat.mod_two_eq_zero_or_one j.val with hj0 | hj1
    · have hP1 := (hspec.2.2.1 hj0).1.1
      have hP2 := (hspec.2.2.1 hj0).1.2
      have hsubP : ∀ y ∈ factorKSetNat j.val a, inPLane y := by
        fin_cases a
        · simp [factorKSetNat]
        · exact hP1
        · exact hP2
        · intro y hy
          simp only [factorKSetNat, Finset.mem_symmDiff] at hy
          rcases hy with ⟨h, _⟩ | ⟨h, _⟩ <;> [exact hP1 y h; exact hP2 y h]
      have hinter0 : factorKSet m j a ∩ qLaneSet m = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro x hx
        rw [Finset.mem_inter, factorKSet, mem_finSetOfNat, qLaneSet, Finset.mem_filter] at hx
        exact hx.2.2 (hsubP x.val hx.1)
      rw [hinter0, Finset.card_empty]; exact ⟨0, rfl⟩
    · have hQ1 := (hspec.2.2.2.1 hj1).1.1
      have hQ2 := (hspec.2.2.2.1 hj1).1.2
      have hev1 := (hspec.2.2.2.1 hj1).2.1
      have hev2 : Even (genSet2Nat j.val).card := hspec.1 ▸ hev1
      have hsubQ : factorKSet m j a ⊆ qLaneSet m := by
        intro x hx
        rw [factorKSet, mem_finSetOfNat] at hx
        rw [qLaneSet, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        fin_cases a
        · simp [factorKSetNat] at hx
        · exact hQ1 x.val hx
        · exact hQ2 x.val hx
        · simp only [factorKSetNat, Finset.mem_symmDiff] at hx
          rcases hx with ⟨h, _⟩ | ⟨h, _⟩ <;> [exact hQ1 x.val h; exact hQ2 x.val h]
      rw [Finset.inter_eq_left.mpr hsubQ]
      fin_cases a
      · simp [factorKSet, factorKSetNat, finSetOfNat]
      · simp only [factorKSet, factorKSetNat]; rw [finSetOfNat_card _ hlt.1]; exact hev1
      · simp only [factorKSet, factorKSetNat]; rw [finSetOfNat_card _ hlt.2]; exact hev2
      · simp only [factorKSet, factorKSetNat]; rw [finSetOfNat_symmDiff]
        exact symmDiff_even_card
          (by rw [finSetOfNat_card _ hlt.1]; exact hev1)
          (by rw [finSetOfNat_card _ hlt.2]; exact hev2)
  have hlist : ∀ L : List (Fin m),
      Even (((L.map (fun j => factorKSet m j (t j))).foldr symmDiff ∅ ∩ qLaneSet m).card) := by
    intro L
    induction L with
    | nil => simp
    | cons hd tl ih =>
        have hdist : (symmDiff (factorKSet m hd (t hd))
              ((tl.map (fun j => factorKSet m j (t j))).foldr symmDiff ∅)) ∩ qLaneSet m =
            symmDiff (factorKSet m hd (t hd) ∩ qLaneSet m)
              (((tl.map (fun j => factorKSet m j (t j))).foldr symmDiff ∅) ∩ qLaneSet m) := by
          ext x
          simp only [Finset.mem_inter, Finset.mem_symmDiff]
          tauto
        simp only [List.map_cons, List.foldr_cons, hdist]
        exact symmDiff_even_card (hfac hd (t hd)) ih
  exact hlist (List.finRange m)

private lemma even_card_iff_even_inter_qLane {m : ℕ} (hm : 1 ≤ m) (t : Fin m → Fin 4) :
    Even (tupleKSet m t).card ↔ Even ((toEvenBlade m (tupleKSet m t) ∩ qLaneSet m).card) := by
  have hevQ := tupleKSet_inter_qLaneSet_even m t
  have hoddQ := qLaneSet_card_odd hm
  dsimp only [toEvenBlade]
  split_ifs with he
  · exact iff_of_true he hevQ
  · refine iff_of_false he ?_
    have hpart : ((tupleKSet m t)ᶜ ∩ qLaneSet m).card + (tupleKSet m t ∩ qLaneSet m).card =
        (qLaneSet m).card := by
      have hdisj : Disjoint ((tupleKSet m t)ᶜ ∩ qLaneSet m) (tupleKSet m t ∩ qLaneSet m) := by
        rw [Finset.disjoint_left]
        intro x hx1 hx2
        rw [Finset.mem_inter, Finset.mem_compl] at hx1
        rw [Finset.mem_inter] at hx2
        exact hx1.1 hx2.1
      have hunion : ((tupleKSet m t)ᶜ ∩ qLaneSet m) ∪ (tupleKSet m t ∩ qLaneSet m) = qLaneSet m := by
        ext x
        simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_compl]
        tauto
      rw [← Finset.card_union_of_disjoint hdisj, hunion]
    rcases hevQ with ⟨a, ha⟩
    rcases hoddQ with ⟨b, hb⟩
    intro hevc
    rcases hevc with ⟨c, hc⟩
    omega

private lemma tupleKSetNat_injective :
    ∀ {m : ℕ}, 1 ≤ m → Function.Injective (tupleKSetNat m)
  | 0, hm, _, _, _ => by omega
  | 1, _, t₁, t₂, heq => by
      have hmem : ∀ (t : Fin 1 → Fin 4) (y : ℕ),
          y ∈ tupleKSetNat 1 t ↔ y ∈ factorKSetNat 0 (t 0) := by
        intro t y
        rw [mem_tupleKSetNat_iff, Fin.sum_univ_one]
        by_cases hy : y ∈ factorKSetNat 0 (t 0) <;> simp [hy]
      have h0 : (0 ∈ factorKSetNat 0 (t₁ 0)) ↔ (0 ∈ factorKSetNat 0 (t₂ 0)) := by
        rw [← hmem t₁ 0, ← hmem t₂ 0, heq]
      have h1 : (1 ∈ factorKSetNat 0 (t₁ 0)) ↔ (1 ∈ factorKSetNat 0 (t₂ 0)) := by
        rw [← hmem t₁ 1, ← hmem t₂ 1, heq]
      ext j
      have hj0 : j = 0 := Fin.eq_zero j
      subst hj0
      generalize t₁ 0 = a at h0 h1 ⊢
      generalize t₂ 0 = b at h0 h1 ⊢
      fin_cases a <;> fin_cases b <;>
        simp [factorKSetNat, genSet1Nat, genSet2Nat, Finset.mem_symmDiff] at h0 h1 ⊢
  | 2, _, t₁, t₂, heq => by
      have hmem : ∀ (t : Fin 2 → Fin 4) (y : ℕ),
          y ∈ tupleKSetNat 2 t ↔
            Xor (y ∈ factorKSetNat 0 (t 0)) (y ∈ factorKSetNat 1 (t 1)) := by
        intro t y
        rw [mem_tupleKSetNat_iff, Fin.sum_univ_two]
        by_cases hy0 : y ∈ factorKSetNat 0 (t 0) <;>
          by_cases hy1 : y ∈ factorKSetNat 1 (t 1) <;>
          simp [hy0, hy1, Xor]
      have h_no1 : ∀ y ∈ ({0, 1} : Finset ℕ), ∀ a : Fin 4, y ∉ factorKSetNat 1 a := by
        intro y hy a
        fin_cases a <;>
          simp [factorKSetNat, genSet1Nat, genSet2Nat] at hy ⊢ <;>
          rcases hy with rfl | rfl <;> decide
      have h_no0 : ∀ y ∈ ({2, 3} : Finset ℕ), ∀ a : Fin 4, y ∉ factorKSetNat 0 a := by
        intro y hy a
        fin_cases a <;>
          simp [factorKSetNat, genSet1Nat, genSet2Nat] at hy ⊢ <;>
          rcases hy with rfl | rfl <;> decide
      have hf0 : ∀ y ∈ ({0, 1} : Finset ℕ),
          (y ∈ factorKSetNat 0 (t₁ 0)) ↔ (y ∈ factorKSetNat 0 (t₂ 0)) := by
        intro y hy
        have h1₁ := h_no1 y hy (t₁ 1)
        have h1₂ := h_no1 y hy (t₂ 1)
        have hiff := congrArg (y ∈ ·) heq
        rw [hmem t₁ y, hmem t₂ y] at hiff
        simp [Xor, h1₁, h1₂] at hiff
        exact hiff
      have hf1 : ∀ y ∈ ({2, 3} : Finset ℕ),
          (y ∈ factorKSetNat 1 (t₁ 1)) ↔ (y ∈ factorKSetNat 1 (t₂ 1)) := by
        intro y hy
        have h0₁ := h_no0 y hy (t₁ 0)
        have h0₂ := h_no0 y hy (t₂ 0)
        have hiff := congrArg (y ∈ ·) heq
        rw [hmem t₁ y, hmem t₂ y] at hiff
        simp [Xor, h0₁, h0₂] at hiff
        exact hiff
      have ht0 : t₁ 0 = t₂ 0 := by
        have h0 := hf0 0 (by simp)
        have h1 := hf0 1 (by simp)
        generalize t₁ 0 = a at h0 h1 ⊢
        generalize t₂ 0 = b at h0 h1 ⊢
        fin_cases a <;> fin_cases b <;>
          simp [factorKSetNat, genSet1Nat, genSet2Nat, Finset.mem_symmDiff] at h0 h1 ⊢
      have ht1 : t₁ 1 = t₂ 1 := by
        have h2 := hf1 2 (by simp)
        have h3 := hf1 3 (by simp)
        generalize t₁ 1 = a at h2 h3 ⊢
        generalize t₂ 1 = b at h2 h3 ⊢
        fin_cases a <;> fin_cases b <;>
          simp [factorKSetNat, genSet1Nat, genSet2Nat, Finset.mem_symmDiff] at h2 h3 ⊢
      funext j
      fin_cases j
      · exact ht0
      · exact ht1
  | k + 3, _, t₁, t₂, heq => by
      let m := k + 2
      have hm2 : 2 ≤ m := by omega
      have ih := tupleKSetNat_injective (m := m) (by omega)
      have htop_disj : ∀ (y : ℕ), (y = 2 * m + 1 ∨ y = 2 * m + 2) →
          ∀ j : Fin m, ∀ a : Fin 4, y ∉ factorKSetNat j.val a := by
        intro y hy j a hjmem
        have hb := factorKSetNat_lt_bound m j a hjmem
        omega
      have hmem_split : ∀ (t : Fin (m + 1) → Fin 4) (y : ℕ),
          y ∈ tupleKSetNat (m + 1) t ↔
            (y ∈ tupleKSetNat m (t ∘ Fin.castSucc) ↔ y ∉ factorKSetNat m (t (Fin.last m))) := by
        intro t y
        rw [mem_tupleKSetNat_iff, mem_tupleKSetNat_iff, Fin.sum_univ_castSucc]
        simp only [Fin.val_castSucc, Fin.val_last, Function.comp_apply]
        by_cases hy : y ∈ factorKSetNat m (t (Fin.last m))
        · simp only [hy, ↓reduceIte, not_true_eq_false, iff_false]
          constructor
          · rintro ⟨q, hq⟩ ⟨p, hp⟩; omega
          · intro hnot
            rcases Nat.even_or_odd (∑ x : Fin m, if y ∈ factorKSetNat (↑x) (t x.castSucc) then 1 else 0) with ⟨p, hp⟩ | ho
            · exact ⟨p, by omega⟩
            · exact False.elim (hnot ho)
        · simp only [hy, ↓reduceIte, add_zero, not_false_eq_true, iff_true]
      have htop_iff : ∀ y, (y = 2 * m + 1 ∨ y = 2 * m + 2) →
          ((y ∈ factorKSetNat m (t₁ (Fin.last m))) ↔ (y ∈ factorKSetNat m (t₂ (Fin.last m)))) := by
        intro y hy
        have h1 : ∀ t : Fin (m + 1) → Fin 4,
            y ∉ tupleKSetNat m (t ∘ Fin.castSucc) := fun t hm' => by
          have hb := tupleKSetNat_lt_bound m (t ∘ Fin.castSucc) hm'; omega
        have he := congrArg (y ∈ ·) heq
        rw [hmem_split t₁ y, hmem_split t₂ y] at he
        simpa [h1 t₁, h1 t₂] using he
      have hpattern : ∀ a : Fin 4,
          (2 * m + 1 ∈ factorKSetNat m a ↔ (a = 1 ∨ a = 3)) ∧
          (2 * m + 2 ∈ factorKSetNat m a ↔ (a = 2 ∨ a = 3)) := by
        intro a
        have hm_sub : ∃ k' : ℕ, m = k' + 2 := ⟨k, rfl⟩
        rcases hm_sub with ⟨k', hmk⟩
        rw [hmk]
        by_cases hpar : k' % 2 = 0
        · have hk2 : 2 * (k' + 2) + 1 = 4 * (k' / 2) + 5 := by omega
          have hk3 : 2 * (k' + 2) + 2 = 4 * (k' / 2) + 6 := by omega
          have h5not : 4 * (k' / 2) + 5 ∉ pPool (k' / 2) := fun h => by
            have := (pPool_spec (k' / 2)).1 _ h; omega
          have h6not : 4 * (k' / 2) + 6 ∉ pPool (k' / 2) := fun h => by
            have := (pPool_spec (k' / 2)).1 _ h; omega
          rw [hk2, hk3]
          fin_cases a
          · simp [factorKSetNat]
          · simp [factorKSetNat, genSet1Nat, hpar, h6not]
          · simp [factorKSetNat, genSet2Nat, hpar, h5not]
          · simp [factorKSetNat, genSet1Nat, genSet2Nat, hpar, Finset.mem_symmDiff, h5not, h6not]
        · have hif : (k' % 2 = 0) ↔ False := by simp [hpar]
          have hk2 : 2 * (k' + 2) + 1 = 4 * (k' / 2) + 7 := by omega
          have hk3 : 2 * (k' + 2) + 2 = 4 * (k' / 2) + 8 := by omega
          have h7not : 4 * (k' / 2) + 7 ∉ qPool (k' / 2) := fun h => by
            have := (qPool_spec (k' / 2)).1 _ h; omega
          have h8not : 4 * (k' / 2) + 8 ∉ qPool (k' / 2) := fun h => by
            have := (qPool_spec (k' / 2)).1 _ h; omega
          rw [hk2, hk3]
          fin_cases a
          · simp [factorKSetNat]
          · simp [factorKSetNat, genSet1Nat, hif, h8not]
          · simp [factorKSetNat, genSet2Nat, hif, h7not]
          · simp [factorKSetNat, genSet1Nat, genSet2Nat, hif, Finset.mem_symmDiff, h7not, h8not]
      have hlast : t₁ (Fin.last m) = t₂ (Fin.last m) := by
        have h_odd1 := htop_iff (2 * m + 1) (Or.inl rfl)
        have h_odd2 := htop_iff (2 * m + 2) (Or.inr rfl)
        rw [(hpattern (t₁ (Fin.last m))).1, (hpattern (t₂ (Fin.last m))).1] at h_odd1
        rw [(hpattern (t₁ (Fin.last m))).2, (hpattern (t₂ (Fin.last m))).2] at h_odd2
        generalize t₁ (Fin.last m) = a at h_odd1 h_odd2 ⊢
        generalize t₂ (Fin.last m) = b at h_odd1 h_odd2 ⊢
        fin_cases a <;> fin_cases b <;> simp at h_odd1 h_odd2 ⊢
      have hpref : tupleKSetNat m (t₁ ∘ Fin.castSucc) = tupleKSetNat m (t₂ ∘ Fin.castSucc) := by
        ext y
        have he := congrArg (y ∈ ·) heq
        rw [hmem_split t₁ y, hmem_split t₂ y, hlast] at he
        tauto
      have hsub := ih hpref
      funext j
      refine Fin.lastCases hlast (fun j' => congrFun hsub j') j

/-- **Clifford (1878, `p. 358`) Complete `4^m = 2^(2m)` Even-Blade Factorization Bijection**:
for every `m ≥ 1`, the `4^m` products of `m` mutually commuting quaternion factor generators
enumerate all `2^(2m)` even basis blades of `Cl⁰(0, 2m+1)` bijectively. -/
theorem evenSupportOfTuple_bijective {m : ℕ} (hm : 1 ≤ m) :
    Function.Bijective (evenSupportOfTuple m) := by
  have hcard : Fintype.card (Fin m → Fin 4) =
      Fintype.card {S : Finset (Fin (2 * m + 1)) // Even S.card} := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, card_evenFinset_subtype (2 * m)]
    calc
      4 ^ m = (2 ^ 2) ^ m := by norm_num
      _ = 2 ^ (2 * m) := (pow_mul 2 2 m).symm
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, hcard⟩
  intro t₁ t₂ ht
  have hev_eq : toEvenBlade m (tupleKSet m t₁) = toEvenBlade m (tupleKSet m t₂) :=
    congrArg Subtype.val ht
  have hparity : Even (tupleKSet m t₁).card ↔ Even (tupleKSet m t₂).card := by
    rw [even_card_iff_even_inter_qLane hm t₁, even_card_iff_even_inter_qLane hm t₂, hev_eq]
  have hset_eq : tupleKSet m t₁ = tupleKSet m t₂ := by
    by_cases he₁ : Even (tupleKSet m t₁).card
    · have he₂ : Even (tupleKSet m t₂).card := hparity.mp he₁
      simpa [toEvenBlade, he₁, he₂] using hev_eq
    · have he₂ : ¬ Even (tupleKSet m t₂).card := fun h => he₁ (hparity.mpr h)
      have hc : (tupleKSet m t₁)ᶜ = (tupleKSet m t₂)ᶜ := by
        simpa [toEvenBlade, he₁, he₂] using hev_eq
      exact compl_inj_iff.mp hc
  rw [tupleKSet_eq_finSetOfNat, tupleKSet_eq_finSetOfNat] at hset_eq
  exact tupleKSetNat_injective hm
    (finSetOfNat_inj (fun y hy => tupleKSetNat_lt_bound m t₁ hy)
      (fun y hy => tupleKSetNat_lt_bound m t₂ hy) hset_eq)

end GeneralOddQuaternionFactorization

section EvenDoublingAndBridgeVIII

/-- Even-dimensional Clifford pseudoscalar `ω₂ₘ = ι₀ ι₁ ⋯ ι_{2m-1}` in `Cl(0, 2m)` (`p. 358`). -/
def ωEven (R : Type*) [CommRing R] (m : ℕ) :
    CliffordAlgebra (cliffordNegSqForm R (2 * m)) :=
  cBlade R (2 * m) Finset.univ

theorem ωEven_mem_even (R : Type*) [CommRing R] (m : ℕ) :
    ωEven R m ∈ CliffordAlgebra.even (cliffordNegSqForm R (2 * m)) := by
  exact cBlade_mem_even R (2 * m) ⟨m, by rw [Finset.card_univ, Fintype.card_fin, two_mul]⟩

theorem ωEven_sq (R : Type*) [CommRing R] (m : ℕ) :
    ωEven R m * ωEven R m = ((-1 : R) ^ m) • 1 := by
  have h := cBlade_sq R (2 * m) Finset.univ
  have hcard : (Finset.univ : Finset (Fin (2 * m))).card = 2 * m := by simp
  rw [hcard] at h
  have hmod : 2 * m * (2 * m + 1) / 2 ≡ m [MOD 2] := by
    have hnum : 2 * m * (2 * m + 1) = 2 * (m * (2 * m + 1)) := by ring
    rw [hnum, Nat.mul_div_right _ (by decide), Nat.ModEq]
    have hmul : m * (2 * m + 1) = 2 * (m * m) + m := by ring
    rw [hmul, Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_mod]
  simpa [ωEven, neg_one_pow_eq_of_modEq hmod] using h

theorem ωEven_comm_even_cBlade (R : Type*) [CommRing R] (m : ℕ)
    {S : Finset (Fin (2 * m))} (hS : Even S.card) :
    Commute (ωEven R m) (cBlade R (2 * m) S) := by
  change ωEven R m * cBlade R (2 * m) S = cBlade R (2 * m) S * ωEven R m
  have hsw := (cBlade_mul_swap_overlap R (2 * m) Finset.univ S).2
  have hcard : (Finset.univ : Finset (Fin (2 * m))).card = 2 * m := by simp
  rw [hcard, Finset.univ_inter] at hsw
  rcases hS with ⟨k, hk⟩
  have hmod : 2 * m * S.card - S.card ^ 2 ≡ 0 [MOD 2] := by
    rw [hk]
    have h2m : 2 * m * (k + k) = 2 * (2 * m * k) := by ring
    have hk2 : (k + k) ^ 2 = 2 * (2 * (k * k)) := by ring
    rw [h2m, hk2, ← Nat.mul_sub_left_distrib, Nat.ModEq]
    simp
  rw [neg_one_pow_eq_of_modEq hmod] at hsw
  simpa [ωEven] using hsw

theorem ωEven_anticomm_cGen (R : Type*) [CommRing R] (m : ℕ) (r : Fin (2 * m)) :
    cGen R (2 * m) r * ωEven R m = -(ωEven R m * cGen R (2 * m) r) := by
  have h := cGen_mul_cBlade R (2 * m) r Finset.univ
  simp only [Finset.card_fin, Finset.mem_univ, ↓reduceIte] at h
  rw [pow_add, pow_mul] at h
  simpa [ωEven] using h

/-- Explicit `2^(2m-1) = 2^(2m-2) + 2^(2m-2)` doubling bijection of even basis blades of `Cl⁰(0, 2m)`
generated by adjoining `ω₂ₘ` (`p. 358`). -/
def evenDoublingEquiv {m : ℕ} (hm : 1 ≤ m) :
    ({T : Finset (Fin (2 * m - 1)) // Even T.card} ⊕
      {T : Finset (Fin (2 * m - 1)) // Even T.card}) ≃
    {S : Finset (Fin (2 * m)) // Even S.card} where
  toFun
    | Sum.inl T => ⟨T.1.map (Fin.castLEEmb (by omega)), by simpa using T.2⟩
    | Sum.inr T =>
        ⟨(T.1.map (Fin.castLEEmb (by omega)))ᶜ, by
          rw [Finset.card_compl, Finset.card_map, Fintype.card_fin]
          rcases T.2 with ⟨k, hk⟩
          exact ⟨m - k, by omega⟩⟩
  invFun S :=
    let lastIdx : Fin (2 * m) := ⟨2 * m - 1, by omega⟩
    let castEmb : Fin (2 * m - 1) ↪ Fin (2 * m) := Fin.castLEEmb (by omega)
    if hlast : lastIdx ∈ S.1 then
      Sum.inr ⟨Finset.univ.filter (fun x : Fin (2 * m - 1) => castEmb x ∈ S.1ᶜ), by
        have hmap : (Finset.univ.filter (fun x : Fin (2 * m - 1) => castEmb x ∈ S.1ᶜ)).map castEmb =
            S.1ᶜ := by
          ext y
          simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
            Fin.castLEEmb_apply, Finset.mem_compl, castEmb]
          constructor
          · rintro ⟨x, hx, rfl⟩; exact hx
          · intro hy
            have hne : y ≠ lastIdx := fun h => hy (h ▸ hlast)
            have hlt : y.val < 2 * m - 1 := by
              have := y.isLt
              have hne_v : y.val ≠ 2 * m - 1 := fun h => hne (Fin.ext h)
              omega
            exact ⟨⟨y.val, hlt⟩, hy, Fin.ext rfl⟩
        rw [← Finset.card_map castEmb, hmap, Finset.card_compl, Fintype.card_fin]
        rcases S.2 with ⟨k, hk⟩
        exact ⟨m - k, by omega⟩⟩
    else
      Sum.inl ⟨Finset.univ.filter (fun x : Fin (2 * m - 1) => castEmb x ∈ S.1), by
        have hmap : (Finset.univ.filter (fun x : Fin (2 * m - 1) => castEmb x ∈ S.1)).map castEmb =
            S.1 := by
          ext y
          simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
            Fin.castLEEmb_apply, castEmb]
          constructor
          · rintro ⟨x, hx, rfl⟩; exact hx
          · intro hy
            have hne : y ≠ lastIdx := fun h => hlast (by rw [← h]; exact hy)
            have hlt : y.val < 2 * m - 1 := by
              have := y.isLt
              have hne_v : y.val ≠ 2 * m - 1 := fun h => hne (Fin.ext h)
              omega
            exact ⟨⟨y.val, hlt⟩, hy, Fin.ext rfl⟩
        rw [← Finset.card_map castEmb, hmap]
        exact S.2⟩
  left_inv s := by
    rcases s with T | T
    · simp only [Fin.castLEEmb_apply]
      have hlast : (⟨2 * m - 1, by omega⟩ : Fin (2 * m)) ∉ T.1.map (Fin.castLEEmb (by omega)) := by
        simp only [Finset.mem_map, Fin.castLEEmb_apply, not_exists, not_and]
        intro x _ h
        have hv : x.val = 2 * m - 1 := congrArg Fin.val h
        have hx := x.isLt
        omega
      simp only [hlast, ↓reduceDIte]
      congr 1; ext1; ext x
      simp
    · simp only [Fin.castLEEmb_apply]
      have hlast : (⟨2 * m - 1, by omega⟩ : Fin (2 * m)) ∈ (T.1.map (Fin.castLEEmb (by omega)))ᶜ := by
        rw [Finset.mem_compl]
        simp only [Finset.mem_map, Fin.castLEEmb_apply, not_exists, not_and]
        intro x _ h
        have hv : x.val = 2 * m - 1 := congrArg Fin.val h
        have hx := x.isLt
        omega
      simp only [hlast, ↓reduceDIte]
      congr 1; ext1; ext x
      simp
  right_inv S := by
    rcases S with ⟨S, hS⟩
    dsimp only
    let lastIdx : Fin (2 * m) := ⟨2 * m - 1, by omega⟩
    let castEmb : Fin (2 * m - 1) ↪ Fin (2 * m) := Fin.castLEEmb (by omega)
    split_ifs with hlast
    · ext1; ext y
      simp only [Finset.mem_compl, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
        Fin.castLEEmb_apply]
      constructor
      · intro hy
        by_contra hy_not
        have hlt : y.val < 2 * m - 1 := by
          have := y.isLt
          by_cases hyeq : y.val = 2 * m - 1
          · exact False.elim (hy_not ((show y = lastIdx from Fin.ext hyeq) ▸ hlast))
          · omega
        exact hy ⟨⟨y.val, hlt⟩, hy_not, Fin.ext rfl⟩
      · rintro hyS ⟨x, hx, hxy⟩
        rw [← hxy] at hyS
        exact hx hyS
    · ext1; ext y
      simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.castLEEmb_apply]
      constructor
      · rintro ⟨x, hx, rfl⟩; exact hx
      · intro hyS
        have hne : y ≠ lastIdx := fun h => hlast (by dsimp [lastIdx] at h; rw [← h]; exact hyS)
        have hlt : y.val < 2 * m - 1 := by
          have := y.isLt
          have hne_v : y.val ≠ 2 * m - 1 := fun h => hne (Fin.ext h)
          omega
        exact ⟨⟨y.val, hlt⟩, hyS, Fin.ext rfl⟩

theorem ωEven_mul_inl_eq_signed_inr (R : Type*) [CommRing R] {m : ℕ} (hm : 1 ≤ m)
    (T : {T : Finset (Fin (2 * m - 1)) // Even T.card}) :
    ∃ s : ℤˣ, ωEven R m * cBlade R (2 * m) (evenDoublingEquiv hm (Sum.inl T)).1 =
      ((s : ℤ) : R) • cBlade R (2 * m) (evenDoublingEquiv hm (Sum.inr T)).1 := by
  have hsym : symmDiff (Finset.univ : Finset (Fin (2 * m)))
      (evenDoublingEquiv hm (Sum.inl T)).1 = (evenDoublingEquiv hm (Sum.inr T)).1 := by
    ext x; simp [evenDoublingEquiv, Finset.mem_symmDiff]
  simpa [ωEven, hsym] using
    cBlade_mul_cBlade_eq_signed_symmDiff R (2 * m) Finset.univ
      (evenDoublingEquiv hm (Sum.inl T)).1

/-- **Bridge VIII (Part A)**: `Cl(0, n)` embeds isomorphically onto the even subalgebra
`Cl⁰(0, n+1)` via Mathlib's `CliffordAlgebra.equivEven` (`p. 358`). -/
def cliffordToEvenAlgEquiv (R : Type*) [CommRing R] (n : ℕ) :
    CliffordAlgebra (cliffordNegSqForm R n) ≃ₐ[R]
      CliffordAlgebra.even (CliffordAlgebra.EquivEven.Q' (cliffordNegSqForm R n)) :=
  CliffordAlgebra.equivEven (cliffordNegSqForm R n)

theorem cliffordNegSqForm_snoc_eq_equivEvenQ' (R : Type*) [CommRing R] (n : ℕ)
    (p : (Fin n → R) × R) :
    cliffordNegSqForm R (n + 1) (Fin.snoc p.1 p.2) =
      CliffordAlgebra.EquivEven.Q' (cliffordNegSqForm R n) p := by
  rw [cliffordNegSqForm_apply, Fin.sum_univ_castSucc, CliffordAlgebra.EquivEven.Q'_apply,
    cliffordNegSqForm_apply]
  simp [Fin.snoc_castSucc, Fin.snoc_last, sub_eq_add_neg]
  rw [add_comm]

theorem ωEven_two_eq_ω₄ (R : Type*) [CommRing R] : ωEven R 2 = ω₄ R := by
  unfold ωEven ω₄
  rfl

/-- Chiral positive Peirce idempotent `e₊ = (1 + ω₄) / 2` in `Cl⁰(0, 4)` (`p. 358`). -/
def biquatIdempPlus : CliffordAlgebra (cliffordNegSqForm ℝ 4) :=
  (1 / 2 : ℝ) • (1 + ωEven ℝ 2)

/-- Chiral negative Peirce idempotent `e₋ = (1 - ω₄) / 2` in `Cl⁰(0, 4)` (`p. 358`). -/
def biquatIdempMinus : CliffordAlgebra (cliffordNegSqForm ℝ 4) :=
  (1 / 2 : ℝ) • (1 - ωEven ℝ 2)

/-- **Bridge VIII (Part B — Chiral Peirce Idempotent Splitting)**:
in Clifford's elliptic biquaternion even algebra `Cl⁰(0, 4)`, `(1 ± ω₄)/2` form a complete
orthogonal pair of nonzero chiral idempotents (`Cl⁰(0, 4) ≅ ℍ ⊕ ℍ`, `pp. 354, 358`). -/
theorem biquat_chiral_peirce_decomposition :
    biquatIdempPlus ∈ CliffordAlgebra.even (cliffordNegSqForm ℝ 4) ∧
    biquatIdempMinus ∈ CliffordAlgebra.even (cliffordNegSqForm ℝ 4) ∧
    biquatIdempPlus * biquatIdempPlus = biquatIdempPlus ∧
    biquatIdempMinus * biquatIdempMinus = biquatIdempMinus ∧
    biquatIdempPlus * biquatIdempMinus = 0 ∧
    biquatIdempMinus * biquatIdempPlus = 0 ∧
    biquatIdempPlus + biquatIdempMinus = 1 ∧
    ωEven ℝ 2 * biquatIdempPlus = biquatIdempPlus ∧
    ωEven ℝ 2 * biquatIdempMinus = -biquatIdempMinus ∧
    biquatIdempPlus ≠ 0 ∧ biquatIdempMinus ≠ 0 := by
  have hωmem : ωEven ℝ 2 ∈ CliffordAlgebra.even (cliffordNegSqForm ℝ 4) := ωEven_mem_even ℝ 2
  have hmemP : biquatIdempPlus ∈ CliffordAlgebra.even (cliffordNegSqForm ℝ 4) :=
    Subalgebra.smul_mem _ (Subalgebra.add_mem _ (Subalgebra.one_mem _) hωmem) _
  have hmemM : biquatIdempMinus ∈ CliffordAlgebra.even (cliffordNegSqForm ℝ 4) :=
    Subalgebra.smul_mem _ (Subalgebra.sub_mem _ (Subalgebra.one_mem _) hωmem) _
  have hωsq : ωEven ℝ 2 * ωEven ℝ 2 = 1 := by
    rw [ωEven_sq ℝ 2]; norm_num
  have hpp : biquatIdempPlus * biquatIdempPlus = biquatIdempPlus := by
    simp only [biquatIdempPlus, smul_mul_smul_comm, mul_add, add_mul, one_mul, mul_one, hωsq]
    module
  have hmm : biquatIdempMinus * biquatIdempMinus = biquatIdempMinus := by
    simp only [biquatIdempMinus, smul_mul_smul_comm, mul_sub, sub_mul, one_mul, mul_one, hωsq]
    module
  have hpm : biquatIdempPlus * biquatIdempMinus = 0 := by
    simp only [biquatIdempPlus, biquatIdempMinus, smul_mul_smul_comm, mul_sub, add_mul, one_mul,
      mul_one, hωsq]
    module
  have hmp : biquatIdempMinus * biquatIdempPlus = 0 := by
    simp only [biquatIdempPlus, biquatIdempMinus, smul_mul_smul_comm, sub_mul, mul_add, one_mul,
      mul_one, hωsq]
    module
  have hadd : biquatIdempPlus + biquatIdempMinus = 1 := by
    simp only [biquatIdempPlus, biquatIdempMinus]
    module
  have hωP : ωEven ℝ 2 * biquatIdempPlus = biquatIdempPlus := by
    simp only [biquatIdempPlus, mul_smul_comm, mul_add, mul_one, hωsq]
    rw [add_comm]
  have hωM : ωEven ℝ 2 * biquatIdempMinus = -biquatIdempMinus := by
    simp only [biquatIdempMinus, mul_smul_comm, mul_sub, mul_one, hωsq, ← smul_neg, neg_sub]
  have hne_set : (∅ : Finset (Fin 4)) ≠ Finset.univ := by decide
  have hrepP : bladeRepr ℝ 4 biquatIdempPlus ∅ = 1 / 2 := by
    have h1 : (1 : CliffordAlgebra (cliffordNegSqForm ℝ 4)) = cBlade ℝ 4 ∅ := (cBlade_empty ℝ 4).symm
    change bladeRepr ℝ 4 ((1 / 2 : ℝ) • ((1 : CliffordAlgebra (cliffordNegSqForm ℝ 4)) +
      cBlade ℝ 4 Finset.univ)) ∅ = 1 / 2
    rw [h1, bladeRepr, map_smul, map_add, LinearMap.smul_apply, LinearMap.add_apply, Pi.smul_apply,
      Pi.add_apply]
    change (1 / 2 : ℝ) * (bladeRepr ℝ 4 (cBlade ℝ 4 ∅) ∅ +
      bladeRepr ℝ 4 (cBlade ℝ 4 Finset.univ) ∅) = 1 / 2
    rw [bladeRepr_cBlade, bladeRepr_cBlade]
    simp [hne_set]
  have hrepM : bladeRepr ℝ 4 biquatIdempMinus ∅ = 1 / 2 := by
    have h1 : (1 : CliffordAlgebra (cliffordNegSqForm ℝ 4)) = cBlade ℝ 4 ∅ := (cBlade_empty ℝ 4).symm
    change bladeRepr ℝ 4 ((1 / 2 : ℝ) • ((1 : CliffordAlgebra (cliffordNegSqForm ℝ 4)) -
      cBlade ℝ 4 Finset.univ)) ∅ = 1 / 2
    rw [h1, bladeRepr, map_smul, map_sub, LinearMap.smul_apply, LinearMap.sub_apply, Pi.smul_apply,
      Pi.sub_apply]
    change (1 / 2 : ℝ) * (bladeRepr ℝ 4 (cBlade ℝ 4 ∅) ∅ -
      bladeRepr ℝ 4 (cBlade ℝ 4 Finset.univ) ∅) = 1 / 2
    rw [bladeRepr_cBlade, bladeRepr_cBlade]
    simp [hne_set]
  have hneP : biquatIdempPlus ≠ 0 := by
    intro hz
    have hc := congrArg (fun X => bladeRepr ℝ 4 X ∅) hz
    rw [hrepP, bladeRepr, map_zero, LinearMap.zero_apply, Pi.zero_apply] at hc
    norm_num at hc
  have hneM : biquatIdempMinus ≠ 0 := by
    intro hz
    have hc := congrArg (fun X => bladeRepr ℝ 4 X ∅) hz
    rw [hrepM, bladeRepr, map_zero, LinearMap.zero_apply, Pi.zero_apply] at hc
    norm_num at hc
  exact ⟨hmemP, hmemM, hpp, hmm, hpm, hmp, hadd, hωP, hωM, hneP, hneM⟩

end EvenDoublingAndBridgeVIII

section CausalPosetAndPentadMasterAtlas

/-- The 12 mathematical archetypes extracted from Grassmann (1877) and Clifford (1878). -/
inductive GrassmannClifford1877_1878Archetype : Type
  | GM1 : GrassmannClifford1877_1878Archetype -- Normalverein, Vector Partial Derivative & Frame Invariance
  | GM2 : GrassmannClifford1877_1878Archetype -- Grundgesetz, SO(3) Half-Turn Centrality & Ampère Countermodel
  | GM3 : GrassmannClifford1877_1878Archetype -- Particle Systems, Barycenter & Radial Potentials
  | GM4 : GrassmannClifford1877_1878Archetype -- Constraints, Virtual Work & Bridge VIa Dyname Splitting
  | GM5 : GrassmannClifford1877_1878Archetype -- Dynamic Pencil, Mean Motion & Kinetic-Energy Minimization
  | GM6 : GrassmannClifford1877_1878Archetype -- Rotating Frame `α²`, Tidal Quadrupole & 5-Harmonic Ocean
  | CL1 : GrassmannClifford1877_1878Archetype -- Quaternions, Rotors, Maxwell Distinctness & Bridge VIIa
  | CL2 : GrassmannClifford1877_1878Archetype -- Elliptic Biquaternions, Polarity & Bridges VIb, VIIb
  | CL3 : GrassmannClifford1877_1878Archetype -- General `Cl(0, n)` Sign & Overlap Laws & Bridge V
  | CL4 : GrassmannClifford1877_1878Archetype -- Odd `(2m+1)`-Way Commuting Quaternion Factorization (`4^m = 2^(2m)`)
  | CL5 : GrassmannClifford1877_1878Archetype -- Even `2m`-Way Double Algebra `(1, ω₂ₘ)` & Bridge VIII
  | CL6 : GrassmannClifford1877_1878Archetype -- 12-Node Causal Poset & 1862–1878 Pentad Synthesis
  deriving DecidableEq, Repr

/-- Downward-closed dependency bitmask on `Fin 12` for the 12 Grassmann–Clifford archetypes. -/
def gc1877_1878Mask : GrassmannClifford1877_1878Archetype → UInt16
  | .GM1 => 1    -- bit 0
  | .GM2 => 3    -- bits 0,1
  | .GM3 => 7    -- bits 0,1,2
  | .GM4 => 15   -- bits 0,1,2,3
  | .GM5 => 19   -- bits 0,1,4
  | .GM6 => 55   -- bits 0,1,2,4,5
  | .CL1 => 64   -- bit 6
  | .CL2 => 192  -- bits 6,7
  | .CL3 => 320  -- bits 6,8
  | .CL4 => 832  -- bits 6,8,9
  | .CL5 => 1984 -- bits 6,7,8,9,10
  | .CL6 => 4095 -- bits 0..11

private lemma gc1877_1878Mask_injective : Function.Injective gc1877_1878Mask := by
  intro a b h
  cases a <;> cases b <;> first | rfl | (simp [gc1877_1878Mask] at h)

instance : LE GrassmannClifford1877_1878Archetype where
  le a b := (gc1877_1878Mask a &&& gc1877_1878Mask b) = gc1877_1878Mask a

instance (a b : GrassmannClifford1877_1878Archetype) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable ((gc1877_1878Mask a &&& gc1877_1878Mask b) = gc1877_1878Mask a))

instance : PartialOrder GrassmannClifford1877_1878Archetype where
  le := (· ≤ ·)
  le_refl a := by cases a <;> decide
  le_trans a b c := by cases a <;> cases b <;> cases c <;> decide
  le_antisymm a b := by cases a <;> cases b <;> decide

theorem gc1877_1878_poset_branching_witnesses :
    (¬ (GrassmannClifford1877_1878Archetype.GM3 ≤ .GM5) ∧
      ¬ (GrassmannClifford1877_1878Archetype.GM5 ≤ .GM3)) ∧
    (¬ (GrassmannClifford1877_1878Archetype.GM4 ≤ .GM6) ∧
      ¬ (GrassmannClifford1877_1878Archetype.GM6 ≤ .GM4)) ∧
    (¬ (GrassmannClifford1877_1878Archetype.CL2 ≤ .CL3) ∧
      ¬ (GrassmannClifford1877_1878Archetype.CL3 ≤ .CL2)) ∧
    (¬ (GrassmannClifford1877_1878Archetype.CL2 ≤ .CL4) ∧
      ¬ (GrassmannClifford1877_1878Archetype.CL4 ≤ .CL2)) := by
  decide

theorem gc1877_1878_all_reach_master (a : GrassmannClifford1877_1878Archetype) :
    a ≤ GrassmannClifford1877_1878Archetype.CL6 := by
  cases a <;> decide

/-- **Grassmann (1877) + Clifford (1878) Pair Master Synthesis (`CL₆`)**:
simultaneously packages `GM₁`–`GM₆`, countermodel `C-GM1`, **Bridge VIa**, `CL₁`–`CL₅`,
countermodel `C-CL1`, and **Bridges V, VIb, VIIa, VIIb, VIII** in a single kernel-checked theorem. -/
theorem grassmann_clifford_1877_1878_master_synthesis :
    -- GM1 & GM2 & C-GM1: frame-invariant gradient, noncommuting SO(3) half-turns, Ampère countermodel
    ((∀ (e ε : Fin 3 → Vec3), IsOrthonormalFrame3 e → IsOrthonormalFrame3 ε →
        ∀ df : Vec3 →ₗ[ℝ] ℝ, grassmannGrad ε df = grassmannGrad e df) ∧
      (halfTurnMatrix ![1, 0, 0] * halfTurnMatrix ![3 / 5, 4 / 5, 0] ≠
        halfTurnMatrix ![3 / 5, 4 / 5, 0] * halfTurnMatrix ![1, 0, 0]) ∧
      ((∀ c : ℝ, ampereForce ![1, 0, 0] ![0, 1, 0] ![1, 0, 0] ≠ c • ![1, 0, 0]) ∧
        ampereForce ![1, 0, 0] ![0, 1, 0] ![1, 0, 0] +
          ampereForce ![0, 1, 0] ![1, 0, 0] (-![1, 0, 0]) ≠ 0)) ∧
    -- GM3 & GM4 & Bridge VIa: system invariants, D'Alembert virtual work & Plücker dyname invariance/splitting
    ((∀ (m : ℕ) (x p : Fin m → Vec3) (c : Fin m → Fin m → ℝ), (∀ i j, c j i = c i j) →
        particleSystemDyname x (fun i => p i + ∑ j : Fin m, c i j • (x j - x i)) =
          particleSystemDyname x p) ∧
      (∀ (m : ℕ) (x p : Fin m → Vec3), (∑ i : Fin m, p i ≠ 0) →
        ∃ d₁ m₁ d₂ m₂ : Vec3, d₁ ≠ 0 ∧ d₂ ≠ 0 ∧
          d₁ ⬝ᵥ m₁ = 0 ∧ d₂ ⬝ᵥ m₂ = 0 ∧
          d₁ + d₂ = ∑ i : Fin m, p i ∧ m₁ + m₂ = ∑ i : Fin m, x i ⨯₃ p i)) ∧
    -- GM5 & GM6: mean-motion kinetic-energy minimization & rotating-frame α² + Laplace 24 → 8 tides
    ((∀ a b p q κ β : ℝ, 0 < κ → 0 < β → κ ≠ β → (p ≠ 0 ∨ q ≠ 0) →
        ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
          (1 / 8 : ℝ) * β ^ 2 * (p ^ 2 + q ^ 2) * T ≤
            totalKineticAntideriv a b p q κ β T - diagKineticAntideriv a b κ T ∧
          0 < totalKineticAntideriv a b p q κ β T - diagKineticAntideriv a b κ T) ∧
      (∀ eHat : Vec3, eHat ⬝ᵥ eHat = 1 → ∀ {n : ℝ}, n ≠ 0 → ∀ v : Vec3,
        rotGen eHat n (rotGen eHat n v) = -(n ^ 2) • v ↔ eHat ⬝ᵥ v = 0) ∧
      (Module.finrank ℝ (Fin 4 → Vec3 × Vec3) = 24 ∧
        ∀ ξ : Vec3, ξ ≠ 0 → Function.Surjective (laplaceVerticalProj ξ) ∧
          Module.finrank ℝ (Fin 4 → ℝ × ℝ) = 8)) ∧
    -- CL1, CL2, CL3 & Bridges V, VIb, VIIa, VIIb: rotor conjugation, biquaternions & sign/overlap laws
    ((∀ (q₀ q₁ q₂ q₃ : ℝ) (v : Fin 3 → ℝ),
        let q := spinQuat3 q₀ q₁ q₂ q₃
        q * (∑ a : Fin 3, v a • cGen ℝ 3 a) * CliffordAlgebra.reverse q =
          ∑ a : Fin 3, (quatRotMatrix q₀ q₁ q₂ q₃ *ᵥ v) a • cGen ℝ 3 a) ∧
      (∀ r : Fin 4, ω₄ ℝ * cGen ℝ 4 r = -(cGen ℝ 4 r * ω₄ ℝ)) ∧
      (∀ d m : Vec3, biquatBivector ℝ d m * biquatBivector ℝ d m =
        algebraMap ℝ _ (-(d ⬝ᵥ d + m ⬝ᵥ m)) -
          (2 * (directionMomentEquiv.symm (d, m)).kleinQ) • ω₄ ℝ) ∧
      (∀ (n : ℕ) (u v : Fin n → ℝ),
        cliffordToExterior n (ι (cliffordNegSqForm ℝ n) u * ι (cliffordNegSqForm ℝ n) v) =
          ExteriorAlgebra.ι ℝ u * ExteriorAlgebra.ι ℝ v -
            algebraMap ℝ (ExteriorAlgebra ℝ (Fin n → ℝ)) (u ⬝ᵥ v)) ∧
      (∀ (n : ℕ) (S T : Finset (Fin n)), (S ∩ T).card ^ 2 ≤ S.card * T.card ∧
        cBlade ℝ n S * cBlade ℝ n T =
          ((-1 : ℝ) ^ (S.card * T.card - (S ∩ T).card ^ 2)) •
            (cBlade ℝ n T * cBlade ℝ n S))) ∧
    -- CL4, CL5, C-CL1 & Bridge VIII: general (2m+1) quaternion factorization, split zero divisors & chiral Peirce
    (((1 + kUnit ℝ 2 0) * (1 - kUnit ℝ 2 0) = 0 ∧
        1 + kUnit ℝ 2 0 ≠ 0 ∧ 1 - kUnit ℝ 2 0 ≠ 0) ∧
      (∀ (m : ℕ), 1 ≤ m →
        (∀ i j : Fin m, i ≠ j → ∀ a b : Fin 4,
          Commute (factorElem ℝ m i a) (factorElem ℝ m j b)) ∧
        Function.Bijective (evenSupportOfTuple m)) ∧
      (biquatIdempPlus * biquatIdempPlus = biquatIdempPlus ∧
        biquatIdempMinus * biquatIdempMinus = biquatIdempMinus ∧
        biquatIdempPlus * biquatIdempMinus = 0 ∧
        biquatIdempPlus + biquatIdempMinus = 1 ∧
        biquatIdempPlus ≠ 0 ∧ biquatIdempMinus ≠ 0)) := by
  refine ⟨⟨grassmannGrad_frame_invariant, so3_halfTurn_noncomm,
      grassmann_footnote_p227_ampere_countermodel⟩,
    ⟨fun _ x p c hc => particleSystemDyname_add_internal_eq x p c hc,
      fun _ x p hp => particleSystemDyname_two_force_splitting x p hp⟩,
    ⟨fun a b p q κ β hκ hβ hne hpq =>
        (meanMotion_strictly_minimizes_integrated_kinetic_energy a b p q κ β hκ hβ hne hpq).2,
      fun eHat he n hn v => rotGen_sq_pure_neg_iff eHat he hn v,
      ⟨tidal24ConstSpace_finrank, laplaceHeightSpace_finrank_and_surjective⟩⟩,
    ⟨rotor_conjugation_eq_quatRotMatrix, (ω₄_polar_points_scalar_versors ℝ).1,
      biquatBivector_sq_plucker_kleinQ, bridgeV_grassmann_clifford_polar_scalar,
      cBlade_mul_swap_overlap ℝ⟩,
    ⟨fiveWay_split_quaternion_zero_divisors,
      fun m hm => ⟨fun i j hij a b => factorElem_comm_of_ne ℝ m hij a b,
        evenSupportOfTuple_bijective hm⟩,
      ⟨biquat_chiral_peirce_decomposition.2.2.1,
        biquat_chiral_peirce_decomposition.2.2.2.1,
        biquat_chiral_peirce_decomposition.2.2.2.2.1,
        biquat_chiral_peirce_decomposition.2.2.2.2.2.2.1,
        biquat_chiral_peirce_decomposition.2.2.2.2.2.2.2.2.2.1,
        biquat_chiral_peirce_decomposition.2.2.2.2.2.2.2.2.2.2⟩⟩⟩

/-- **1862–1878 Five-Work Pentad Master Synthesis**:
unites all five foundational works across **Grassmann (1862)**, **Plücker (1868/1869)**,
**Klein (1872)**, **Grassmann (1877)**, and **Clifford (1878)**, together with all eight
cross-work bridges (**Bridges I–VIII**), in one kernel-checked theorem. -/
theorem grassmann1862_plucker1868_klein1872_grassmann1877_clifford1878_pentad_synthesis :
    -- 1. Grassmann (1862) + Plücker (1868/1869) + Klein (1872) Trilogy & Bridges I–IV
    ((sigPos circleBilin.toQuadraticMap = 1 ∧ sigNeg circleBilin.toQuadraticMap = 3) ∧
      (Module.finrank ℝ (symmMat6Submodule ℝ ⧸ Submodule.span ℝ {kleinSymmMatrix}) = 20) ∧
      (∀ q₀ q₁ q₂ q₃ : ℝ, q₀ ^ 2 + q₁ ^ 2 + q₂ ^ 2 + q₃ ^ 2 = 1 →
        (quatRotMatrix q₀ q₁ q₂ q₃)ᵀ * quatRotMatrix q₀ q₁ q₂ q₃ = 1 ∧
          (quatRotMatrix q₀ q₁ q₂ q₃).det = 1) ∧
      (∀ (C P : Plucker6 ℝ) (G : Matrix (Fin 4) (Fin 4) ℝ), G.IsSymm →
        ∀ (x y : Fin 4 → ℝ) (k : Fin 4),
          conjugatePolar C (conjugatePolar C P) = Plucker6.scale (C.kleinQ ^ 2) P ∧
          (coordinates (rayPlucker x y) ⬝ᵥ (secondCompound G *ᵥ coordinates (rayPlucker x y)) =
            (x ⬝ᵥ (G *ᵥ x)) * (y ⬝ᵥ (G *ᵥ y)) - (x ⬝ᵥ (G *ᵥ y)) ^ 2) ∧
          (coneChartMatrix (secondCompound G) x k).det =
            (x k) ^ 2 * kummerSingularQuartic (secondCompound G) x)) ∧
    -- 2. Bridge V + Grassmann (1877) Bridge VIa + Clifford (1878) Bridges VIb, VIIa, VIIb, VIII
    ((∀ (m : ℕ) (x p : Fin m → Vec3), (∑ i : Fin m, p i ≠ 0) →
        ∃ d₁ m₁ d₂ m₂ : Vec3, d₁ ≠ 0 ∧ d₂ ≠ 0 ∧
          d₁ ⬝ᵥ m₁ = 0 ∧ d₂ ⬝ᵥ m₂ = 0 ∧
          d₁ + d₂ = ∑ i : Fin m, p i ∧ m₁ + m₂ = ∑ i : Fin m, x i ⨯₃ p i) ∧
      (∀ (n : ℕ) (u v : Fin n → ℝ),
        cliffordToExterior n (ι (cliffordNegSqForm ℝ n) u * ι (cliffordNegSqForm ℝ n) v) =
          ExteriorAlgebra.ι ℝ u * ExteriorAlgebra.ι ℝ v -
            algebraMap ℝ (ExteriorAlgebra ℝ (Fin n → ℝ)) (u ⬝ᵥ v)) ∧
      (∀ d m : Vec3, biquatBivector ℝ d m * biquatBivector ℝ d m =
        algebraMap ℝ _ (-(d ⬝ᵥ d + m ⬝ᵥ m)) -
          (2 * (directionMomentEquiv.symm (d, m)).kleinQ) • ω₄ ℝ) ∧
      (∀ (q₀ q₁ q₂ q₃ : ℝ) (v : Fin 3 → ℝ),
        let q := spinQuat3 q₀ q₁ q₂ q₃
        q * (∑ a : Fin 3, v a • cGen ℝ 3 a) * CliffordAlgebra.reverse q =
          ∑ a : Fin 3, (quatRotMatrix q₀ q₁ q₂ q₃ *ᵥ v) a • cGen ℝ 3 a) ∧
      (∀ r : Fin 4, ω₄ ℝ * cGen ℝ 4 r = -(cGen ℝ 4 r * ω₄ ℝ)) ∧
      (∀ (m : ℕ), 1 ≤ m → Function.Bijective (evenSupportOfTuple m)) ∧
      (biquatIdempPlus * biquatIdempPlus = biquatIdempPlus ∧
        biquatIdempMinus * biquatIdempMinus = biquatIdempMinus ∧
        biquatIdempPlus * biquatIdempMinus = 0 ∧
        biquatIdempPlus + biquatIdempMinus = 1)) := by
  exact ⟨⟨grassmann_complete_endmatter_master_synthesis.2.1,
      plucker_neue_geometrie_master_synthesis.2.2.2.2.1,
      klein_erlangen_1872_master_synthesis.2.2.2.2.2.2.2.2.2.2,
      grassmann_plucker_klein_trilogy_synthesis.2.1⟩,
    ⟨fun _ x p hp => particleSystemDyname_two_force_splitting x p hp,
      bridgeV_grassmann_clifford_polar_scalar,
      biquatBivector_sq_plucker_kleinQ,
      rotor_conjugation_eq_quatRotMatrix,
      (ω₄_polar_points_scalar_versors ℝ).1,
      fun m hm => evenSupportOfTuple_bijective hm,
      ⟨biquat_chiral_peirce_decomposition.2.2.1,
        biquat_chiral_peirce_decomposition.2.2.2.1,
        biquat_chiral_peirce_decomposition.2.2.2.2.1,
        biquat_chiral_peirce_decomposition.2.2.2.2.2.2.1⟩⟩⟩

end CausalPosetAndPentadMasterAtlas

end InfoGeometry.Clifford.CliffordQuaternionFactorizationAndMasterAtlas
