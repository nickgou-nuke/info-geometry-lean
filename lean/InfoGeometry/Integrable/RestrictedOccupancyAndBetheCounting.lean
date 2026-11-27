/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Rat.Init
import Mathlib.Data.Sym.Card
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.GroupTheory.Perm.Support
import Mathlib.Order.Fin.Basic
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic

/-!
# Restricted Occupancy, SSYT Bijections, Bethe-State Counting & SU(3) Weyl Alternating Sums

Formalization of the finite combinatorial and algebraic Bethe-state counting results in
Shu, Zhao, Zhu, Zou, *Bethe-state counting and Witten index*, SciPost Phys. 15, 103 (2023):
- Part 1: 2D restricted occupancy (`c_s(L; M)`, Eq. 6), total sum `(2s + 1)^L`, spin-flip duality,
  stabilization for `2s ≥ M`, rank-1 untwisted difference (Eq. 12) & unimodality;
  3D restricted occupancy, SSYT bijection (`SiteProfile` ↔ single-row SSYT of length `2s`),
  total sum `choose (2s + r) r ^ L` (Eq. 9), and Seiberg/Weyl reflection duality (Eqs. 10–11).
- Part 2: Kondo model (Eqs. 16–17), spin-`s` `t`-`J` model & `s = 1/2` Foerster–Karowski identity
  (Eqs. 18–21), and `SU(3)` singular-locus / highest-weight alternating sums (Eqs. 13–15,
  Table 1, and Weyl-character / Vandermonde alternant identification).
-/

namespace InfoGeometry.Integrable.RestrictedOccupancyAndBetheCounting

open Finset

/-! ## Part 1A: 2D Restricted Occupancy Combinatorics -/

/-- Configurations of `M` boxes into `L` sites, each with capacity `twoS` (`0 ≤ n α ≤ 2s`). -/
def restrictedOccupancy2D (twoS L M : ℕ) : Type :=
  { n : Fin L → ℕ // (∀ α, n α ≤ twoS) ∧ ∑ α, n α = M }

instance (twoS L M : ℕ) : DecidableEq (restrictedOccupancy2D twoS L M) :=
  inferInstanceAs (DecidableEq { n : Fin L → ℕ // (∀ α, n α ≤ twoS) ∧ ∑ α, n α = M })

private def restrictedOccupancy2DEquivFin (twoS L M : ℕ) :
    restrictedOccupancy2D twoS L M ≃ { n : Fin L → Fin (twoS + 1) // ∑ α, (n α : ℕ) = M } where
  toFun n :=
    ⟨fun α => ⟨n.1 α, Nat.lt_succ_of_le (n.2.1 α)⟩, by simpa using n.2.2⟩
  invFun n :=
    ⟨fun α => (n.1 α).val, ⟨fun α => Nat.le_of_lt_succ (n.1 α).isLt, n.2⟩⟩
  left_inv _ := Subtype.ext (funext fun _ => rfl)
  right_inv _ := Subtype.ext (funext fun _ => rfl)

instance (twoS L M : ℕ) : Fintype (restrictedOccupancy2D twoS L M) :=
  Fintype.ofEquiv _ (restrictedOccupancy2DEquivFin twoS L M).symm

/-- Canonical empty witness for `restrictedOccupancy2D`. -/
def canonicalRestrictedOccupancy2D : restrictedOccupancy2D 0 0 0 :=
  ⟨Fin.elim0, fun α => Fin.elim0 α, rfl⟩

/-- Truncated geometric polynomial `1 + X + ⋯ + X ^ N` over `ℤ`. -/
noncomputable def truncGeom (N : ℕ) : Polynomial ℤ :=
  ∑ k ∈ Finset.range (N + 1), Polynomial.X ^ k

private lemma truncGeom_pow_coeff_eq_card (twoS L M : ℕ) :
    ((truncGeom twoS) ^ L).coeff M = (Fintype.card (restrictedOccupancy2D twoS L M) : ℤ) := by
  have hgeom : truncGeom twoS = ∑ k : Fin (twoS + 1), Polynomial.X ^ (k : ℕ) := by
    rw [truncGeom, Fin.sum_univ_eq_sum_range]
  rw [hgeom, Fintype.sum_pow, Polynomial.finsetSum_coeff]
  have hprod : ∀ p : Fin L → Fin (twoS + 1),
      (∏ i : Fin L, (Polynomial.X : Polynomial ℤ) ^ (p i : ℕ)) =
        Polynomial.X ^ (∑ i : Fin L, (p i : ℕ)) := by
    intro p
    rw [Finset.prod_pow_eq_pow_sum]
  simp_rw [hprod, Polynomial.coeff_X_pow]
  have hsum :
      (∑ p : Fin L → Fin (twoS + 1), if M = ∑ i : Fin L, (p i : ℕ) then (1 : ℤ) else 0) =
        ((Finset.univ.filter (fun p : Fin L → Fin (twoS + 1) => ∑ α, (p α : ℕ) = M)).card : ℤ) := by
    rw [Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl fun p _ => ?_
    simp [eq_comm]
  rw [hsum, ← Fintype.card_subtype, ← Fintype.card_congr (restrictedOccupancy2DEquivFin twoS L M)]

private noncomputable def restrictedOccupancy2DEquivSym (twoS L d : ℕ) (hd : d ≤ twoS) :
    restrictedOccupancy2D twoS L d ≃ Sym (Fin L) d :=
  let e1 : restrictedOccupancy2D twoS L d ≃ { n : Fin L → ℕ // ∑ α, n α = d } :=
    { toFun := fun n => ⟨n.1, n.2.2⟩
      invFun := fun n =>
        ⟨n.1, fun α => le_trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ α)) (n.2.le.trans hd), n.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  e1.trans (Sym.equivNatSumOfFintype (Fin L) d).symm

/-- Stabilization: for `2s ≥ M`, `c_s(L; M) = choose (L + M - 1) M`. -/
theorem card_restrictedOccupancy2D_of_le (twoS L M : ℕ) (hM : M ≤ twoS) :
    Fintype.card (restrictedOccupancy2D twoS L M) = Nat.choose (L + M - 1) M := by
  classical
  rw [Fintype.card_congr (restrictedOccupancy2DEquivSym twoS L M hM), Sym.card_sym_eq_choose]
  simp

/-- Stabilization in `(L - 1)` binomial form when `1 ≤ L` and `M ≤ 2s`. -/
theorem card_restrictedOccupancy2D_of_le' (twoS L M : ℕ) (hL : 1 ≤ L) (hM : M ≤ twoS) :
    Fintype.card (restrictedOccupancy2D twoS L M) = Nat.choose (L + M - 1) (L - 1) := by
  rw [card_restrictedOccupancy2D_of_le twoS L M hM]
  have hL' : L - 1 + 1 = L := Nat.sub_add_cancel hL
  apply Nat.choose_symm_of_eq_add
  omega

private lemma truncGeom_pow_coeff_eq_multichoose (M L d : ℕ) (hd : d ≤ M) :
    ((truncGeom M) ^ L).coeff d = (Nat.multichoose L d : ℤ) := by
  classical
  rw [truncGeom_pow_coeff_eq_card M L d]
  rw [Fintype.card_congr (restrictedOccupancy2DEquivSym M L d hd)]
  rw [Sym.card_sym_eq_multichoose, Fintype.card_fin]

/-- Unconditional Eq. (6) using `Nat.multichoose` (valid for all `L : ℕ`, including `L = 0`). -/
theorem card_restrictedOccupancy2D_eq_multichoose (twoS L M : ℕ) :
    (Fintype.card (restrictedOccupancy2D twoS L M) : ℤ) =
      ∑ j ∈ Finset.range (L + 1),
        if (twoS + 1) * j ≤ M then
          (-1 : ℤ) ^ j * (Nat.choose L j : ℤ) *
            (Nat.multichoose L (M - (twoS + 1) * j) : ℤ)
        else 0 := by
  rw [← truncGeom_pow_coeff_eq_card twoS L M]
  have h1 : truncGeom twoS * (1 - Polynomial.X) = 1 - Polynomial.X ^ (twoS + 1) := by
    simpa [truncGeom] using geom_sum_mul_neg (Polynomial.X : Polynomial ℤ) (twoS + 1)
  have h2 : (1 - Polynomial.X) * truncGeom M = 1 - Polynomial.X ^ (M + 1) := by
    rw [mul_comm]
    simpa [truncGeom] using geom_sum_mul_neg (Polynomial.X : Polynomial ℤ) (M + 1)
  have hmul :
      truncGeom twoS * (1 - Polynomial.X ^ (M + 1)) =
        (1 - Polynomial.X ^ (twoS + 1)) * truncGeom M := by
    calc
      truncGeom twoS * (1 - Polynomial.X ^ (M + 1))
          = truncGeom twoS * ((1 - Polynomial.X) * truncGeom M) := by rw [← h2]
      _ = (truncGeom twoS * (1 - Polynomial.X)) * truncGeom M := by rw [mul_assoc]
      _ = (1 - Polynomial.X ^ (twoS + 1)) * truncGeom M := by rw [h1]
  have hpow :
      (truncGeom twoS) ^ L * (1 - Polynomial.X ^ (M + 1)) ^ L =
        (1 - Polynomial.X ^ (twoS + 1)) ^ L * (truncGeom M) ^ L := by
    rw [← mul_pow, ← mul_pow, hmul]
  have hsubpow : ∀ (k : ℕ),
      (1 - (Polynomial.X : Polynomial ℤ) ^ k) ^ L =
        ∑ j ∈ Finset.range (L + 1),
          Polynomial.C ((-1 : ℤ) ^ j * (Nat.choose L j : ℤ)) * Polynomial.X ^ (k * j) := by
    intro k
    rw [sub_eq_add_neg, add_comm, add_pow]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hpowX : (-Polynomial.X ^ k) ^ j =
        Polynomial.C ((-1 : ℤ) ^ j) * Polynomial.X ^ (k * j) := by
      rw [neg_eq_neg_one_mul, mul_pow, ← pow_mul, mul_comm k j]
      simp
    rw [one_pow, mul_one, hpowX, ← Polynomial.C_eq_natCast, mul_assoc,
      mul_comm (Polynomial.X ^ (k * j)) (Polynomial.C _), ← mul_assoc, ← Polynomial.C_mul]
  have hlhs : ((truncGeom twoS) ^ L * (1 - Polynomial.X ^ (M + 1)) ^ L).coeff M =
      ((truncGeom twoS) ^ L).coeff M := by
    rw [hsubpow (M + 1), Finset.mul_sum, Polynomial.finsetSum_coeff]
    have hterm : ∀ j ∈ Finset.range (L + 1),
        ((truncGeom twoS) ^ L *
          (Polynomial.C ((-1 : ℤ) ^ j * (Nat.choose L j : ℤ)) *
            Polynomial.X ^ ((M + 1) * j))).coeff M =
          if j = 0 then ((truncGeom twoS) ^ L).coeff M else 0 := by
      intro j _
      rw [← mul_assoc, mul_comm ((truncGeom twoS) ^ L) (Polynomial.C _), mul_assoc,
        Polynomial.coeff_C_mul, mul_comm ((truncGeom twoS) ^ L), Polynomial.coeff_X_pow_mul']
      rcases j with _ | j
      · simp
      · have hgt : ¬ ((M + 1) * (j + 1) ≤ M) := by nlinarith
        simp [hgt]
    rw [Finset.sum_congr rfl hterm]
    simp
  have hrhs : ((1 - Polynomial.X ^ (twoS + 1)) ^ L * (truncGeom M) ^ L).coeff M =
      ∑ j ∈ Finset.range (L + 1),
        if (twoS + 1) * j ≤ M then
          (-1 : ℤ) ^ j * (Nat.choose L j : ℤ) *
            (Nat.multichoose L (M - (twoS + 1) * j) : ℤ)
        else 0 := by
    rw [hsubpow (twoS + 1), Finset.sum_mul, Polynomial.finsetSum_coeff]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul']
    split_ifs with hj
    · rw [truncGeom_pow_coeff_eq_multichoose M L (M - (twoS + 1) * j) (Nat.sub_le _ _)]
    · simp
  rw [← hlhs, hpow, hrhs]

/-- Eq. (6) of Shu et al.: alternating binomial formula for `c_s(L; M)` when `1 ≤ L`. -/
theorem card_restrictedOccupancy2D_eq (twoS L M : ℕ) (hL : 1 ≤ L) :
    (Fintype.card (restrictedOccupancy2D twoS L M) : ℤ) =
      ∑ j ∈ Finset.range (L + 1),
        if (twoS + 1) * j ≤ M then
          (-1 : ℤ) ^ j * (Nat.choose L j : ℤ) *
            (Nat.choose (L + M - 1 - (twoS + 1) * j) (L - 1) : ℤ)
        else 0 := by
  have hL' : L - 1 + 1 = L := Nat.sub_add_cancel hL
  rw [card_restrictedOccupancy2D_eq_multichoose]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with hj
  · have hm : Nat.multichoose L (M - (twoS + 1) * j) =
        Nat.choose (L + M - 1 - (twoS + 1) * j) (L - 1) := by
      rw [Nat.multichoose_eq]
      have hsym : (L + (M - (twoS + 1) * j) - 1).choose (M - (twoS + 1) * j) =
          (L + (M - (twoS + 1) * j) - 1).choose (L - 1) := by
        apply Nat.choose_symm_of_eq_add
        omega
      rw [hsym]
      congr 1
      omega
    rw [hm]
  · rfl

private def restrictedOccupancy2DSigmaEquiv (twoS L : ℕ) :
    (M : Fin (twoS * L + 1)) × restrictedOccupancy2D twoS L M.1 ≃ (Fin L → Fin (twoS + 1)) where
  toFun x α := ⟨x.2.1 α, Nat.lt_succ_of_le (x.2.2.1 α)⟩
  invFun f :=
    let Mval := ∑ α, (f α : ℕ)
    have hM : Mval < twoS * L + 1 := by
      have hsum : ∑ α : Fin L, (f α : ℕ) ≤ ∑ _α : Fin L, twoS :=
        Finset.sum_le_sum fun α _ => Nat.le_of_lt_succ (f α).isLt
      simpa [Mval, Finset.sum_const, smul_eq_mul, mul_comm] using Nat.lt_succ_of_le hsum
    ⟨⟨Mval, hM⟩, ⟨fun α => (f α).val, fun α => Nat.le_of_lt_succ (f α).isLt, rfl⟩⟩
  left_inv x := by
    rcases x with ⟨⟨M, hM⟩, ⟨n, hn1, hn2⟩⟩
    dsimp only at hn2
    subst hn2
    rfl
  right_inv f := by ext α; rfl

/-- Total number of 2D restricted-occupancy states across `M = 0, ..., 2sL` is `(2s + 1) ^ L`. -/
theorem sum_card_restrictedOccupancy2D (twoS L : ℕ) :
    ∑ M ∈ Finset.range (twoS * L + 1), Fintype.card (restrictedOccupancy2D twoS L M) =
      (twoS + 1) ^ L := by
  have hcard := Fintype.card_congr (restrictedOccupancy2DSigmaEquiv twoS L)
  rw [Fintype.card_sigma] at hcard
  rw [← Fin.sum_univ_eq_sum_range (f := fun M => Fintype.card (restrictedOccupancy2D twoS L M))]
  simpa [Fintype.card_pi_const, Fintype.card_fin] using hcard

/-- Spin-flip duality `s_α ↔ -s_α` (`n α ↦ 2s - n α`) on 2D restricted occupancy. -/
def spinFlipEquiv2D (twoS L M : ℕ) (hM : M ≤ twoS * L) :
    restrictedOccupancy2D twoS L M ≃ restrictedOccupancy2D twoS L (twoS * L - M) where
  toFun n :=
    ⟨fun α => twoS - n.1 α,
      fun α => Nat.sub_le twoS (n.1 α),
      by
        have hsum : ∑ α : Fin L, (twoS - n.1 α) + ∑ α : Fin L, n.1 α =
            ∑ _α : Fin L, twoS := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun α _ => Nat.sub_add_cancel (n.2.1 α)
        have hconst : ∑ _α : Fin L, twoS = twoS * L := by
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
            mul_comm L twoS]
        have hn2 : ∑ α : Fin L, n.1 α = M := n.2.2
        dsimp only
        omega⟩
  invFun n :=
    ⟨fun α => twoS - n.1 α,
      fun α => Nat.sub_le twoS (n.1 α),
      by
        have hsum : ∑ α : Fin L, (twoS - n.1 α) + ∑ α : Fin L, n.1 α =
            ∑ _α : Fin L, twoS := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun α _ => Nat.sub_add_cancel (n.2.1 α)
        have hconst : ∑ _α : Fin L, twoS = twoS * L := by
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
            mul_comm L twoS]
        have hn2 : ∑ α : Fin L, n.1 α = twoS * L - M := n.2.2
        have hMM : twoS * L - (twoS * L - M) = M := Nat.sub_sub_self hM
        dsimp only
        omega⟩
  left_inv n := Subtype.ext (funext fun α => Nat.sub_sub_self (n.2.1 α))
  right_inv n := Subtype.ext (funext fun α => Nat.sub_sub_self (n.2.1 α))

/-- Spin-flip symmetry `c_s(L; M) = c_s(L; 2sL - M)` for `M ≤ 2sL`. -/
theorem card_restrictedOccupancy2D_spinFlip (twoS L M : ℕ) (hM : M ≤ twoS * L) :
    Fintype.card (restrictedOccupancy2D twoS L M) =
      Fintype.card (restrictedOccupancy2D twoS L (twoS * L - M)) :=
  Fintype.card_congr (spinFlipEquiv2D twoS L M hM)

private def restrictedOccupancy2DOneEquiv (L M : ℕ) :
    restrictedOccupancy2D 1 L M ≃ { s : Finset (Fin L) // s.card = M } where
  toFun n :=
    ⟨Finset.univ.filter (fun α => n.1 α = 1), by
      have hsum : ∑ α : Fin L, n.1 α =
          ∑ α : Fin L, if n.1 α = 1 then 1 else 0 := by
        refine Finset.sum_congr rfl fun α _ => ?_
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (n.2.1 α) with h | h <;> simp [h]
      have hM : ∑ α : Fin L, n.1 α = M := n.2.2
      rw [hsum] at hM
      simpa [Finset.sum_boole] using hM⟩
  invFun s :=
    ⟨fun α => if α ∈ s.1 then 1 else 0,
      fun α => by dsimp only; split_ifs <;> omega,
      by simp [s.2]⟩
  left_inv n := Subtype.ext (funext fun α => by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (n.2.1 α) with h | h <;> simp [h])
  right_inv s := by
    ext α
    simp

/-- For spin `s = 1/2` (`twoS = 1`), `c_{1/2}(L; M) = choose L M`. -/
theorem card_restrictedOccupancy2D_one (L M : ℕ) :
    Fintype.card (restrictedOccupancy2D 1 L M) = Nat.choose L M := by
  classical
  rw [Fintype.card_congr (restrictedOccupancy2DOneEquiv L M)]
  have heq : { s : Finset (Fin L) // s.card = M } ≃
      (Finset.univ : Finset (Fin L)).powersetCard M :=
    { toFun := fun s => ⟨s.1, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, s.2⟩⟩
      invFun := fun s => ⟨s.1, (Finset.mem_powersetCard.mp s.2).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr heq, Fintype.card_coe, Finset.card_powersetCard, Finset.card_univ,
    Fintype.card_fin]

/-- Eq. (12) of Shu et al.: rank-1 untwisted Bethe-state count `c_s(L; M) - c_s(L; M - 1)`. -/
def rank1UntwistedCount (twoS L M : ℕ) : ℤ :=
  (Fintype.card (restrictedOccupancy2D twoS L M) : ℤ) -
    (Fintype.card (restrictedOccupancy2D twoS L (M - 1)) : ℤ)

private lemma card_restrictedOccupancy2D_zero (twoS L : ℕ) :
    Fintype.card (restrictedOccupancy2D twoS L 0) = 1 := by
  have heq : restrictedOccupancy2D twoS L 0 ≃ Unit :=
    { toFun := fun _ => ()
      invFun := fun _ => ⟨fun _ => 0, fun _ => Nat.zero_le _, by simp⟩
      left_inv := fun n => Subtype.ext (funext fun α => by
        have h0 : ∑ β : Fin L, n.1 β = 0 := n.2.2
        have hle : n.1 α ≤ ∑ β : Fin L, n.1 β :=
          Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ α)
        dsimp only
        omega)
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr heq, Fintype.card_unit]

/-- Telescoping sum of rank-1 untwisted counts over `m = 1, ..., K`. -/
theorem sum_rank1UntwistedCount (twoS L K : ℕ) :
    ∑ m ∈ Finset.Icc 1 K, rank1UntwistedCount twoS L m =
      (Fintype.card (restrictedOccupancy2D twoS L K) : ℤ) - 1 := by
  induction K with
  | zero => simp [card_restrictedOccupancy2D_zero]
  | succ K ih =>
    have hsplit : Finset.Icc 1 (K + 1) = insert (K + 1) (Finset.Icc 1 K) := by
      ext m
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hnot : K + 1 ∉ Finset.Icc 1 K := by simp
    rw [hsplit, Finset.sum_insert hnot, ih, rank1UntwistedCount]
    simp only [Nat.add_sub_cancel]
    ring

private lemma card_restrictedOccupancy2D_succ_len (twoS L M : ℕ) :
    (Fintype.card (restrictedOccupancy2D twoS (L + 1) M) : ℤ) =
      ∑ k ∈ Finset.range (twoS + 1),
        if k ≤ M then (Fintype.card (restrictedOccupancy2D twoS L (M - k)) : ℤ) else 0 := by
  have hpow : (truncGeom twoS) ^ (L + 1) =
      (∑ k ∈ Finset.range (twoS + 1), Polynomial.X ^ k) * (truncGeom twoS) ^ L := by
    rw [pow_succ']
    rfl
  rw [← truncGeom_pow_coeff_eq_card twoS (L + 1) M, hpow,
    Finset.sum_mul, Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Polynomial.coeff_X_pow_mul']
  split_ifs with hk
  · rw [truncGeom_pow_coeff_eq_card twoS L (M - k)]
  · rfl

private lemma card_restrictedOccupancy2D_mono_half_aux (twoS : ℕ) :
    ∀ L M, 1 ≤ M → 2 * M ≤ twoS * L →
      Fintype.card (restrictedOccupancy2D twoS L (M - 1)) ≤
        Fintype.card (restrictedOccupancy2D twoS L M) := by
  intro L
  induction L with
  | zero =>
    intro M hM1 hM2
    omega
  | succ L ih =>
    have hchain : ∀ A B, A ≤ B → 2 * B ≤ twoS * L →
        Fintype.card (restrictedOccupancy2D twoS L A) ≤
          Fintype.card (restrictedOccupancy2D twoS L B) := by
      intro A B hAB hB
      induction B with
      | zero =>
        have hA : A = 0 := Nat.le_zero.mp hAB
        subst hA
        exact le_rfl
      | succ B ihB =>
        rcases eq_or_lt_of_le hAB with rfl | hlt
        · exact le_rfl
        · have hAB' : A ≤ B := Nat.le_of_lt_succ hlt
          have hB' : 2 * B ≤ twoS * L := by omega
          exact le_trans (ihB hAB' hB') (ih (B + 1) (by omega) hB)
    intro M hM1 hM2
    rw [← Int.ofNat_le]
    have hdiff :
        (Fintype.card (restrictedOccupancy2D twoS (L + 1) M) : ℤ) -
          (Fintype.card (restrictedOccupancy2D twoS (L + 1) (M - 1)) : ℤ) =
          (Fintype.card (restrictedOccupancy2D twoS L M) : ℤ) -
            if twoS ≤ M - 1 then
              (Fintype.card (restrictedOccupancy2D twoS L (M - 1 - twoS)) : ℤ)
            else 0 := by
      rw [card_restrictedOccupancy2D_succ_len twoS L M,
        card_restrictedOccupancy2D_succ_len twoS L (M - 1)]
      rw [Finset.sum_range_succ' _ twoS, Finset.sum_range_succ _ twoS]
      have h0 : (if 0 ≤ M then (Fintype.card (restrictedOccupancy2D twoS L (M - 0)) : ℤ) else 0) =
          (Fintype.card (restrictedOccupancy2D twoS L M) : ℤ) := by simp
      have hcancel :
          ∑ k ∈ Finset.range twoS,
            (if k + 1 ≤ M then (Fintype.card (restrictedOccupancy2D twoS L (M - (k + 1))) : ℤ)
              else 0) =
            ∑ k ∈ Finset.range twoS,
              (if k ≤ M - 1 then (Fintype.card (restrictedOccupancy2D twoS L (M - 1 - k)) : ℤ)
                else 0) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        have hiff : k + 1 ≤ M ↔ k ≤ M - 1 := by omega
        by_cases hk : k + 1 ≤ M
        · have hk' : k ≤ M - 1 := hiff.mp hk
          have hsub : M - (k + 1) = M - 1 - k := by omega
          simp [hk, hk', hsub]
        · have hk' : ¬ (k ≤ M - 1) := mt hiff.mpr hk
          simp [hk, hk']
      rw [h0, hcancel]
      ring
    suffices hnonneg :
        0 ≤ (Fintype.card (restrictedOccupancy2D twoS (L + 1) M) : ℤ) -
          (Fintype.card (restrictedOccupancy2D twoS (L + 1) (M - 1)) : ℤ) by
      linarith
    rw [hdiff]
    have hmulL : twoS * (L + 1) = twoS * L + twoS := by ring
    split_ifs with htwoS
    · rw [sub_nonneg, Int.ofNat_le]
      rcases eq_or_ne L 0 with rfl | hLne
      · simp at hM2; omega
      · have hL1 : 1 ≤ L := Nat.one_le_iff_ne_zero.mpr hLne
        have hMle : M ≤ twoS * L := by
          have h1 : twoS ≤ twoS * L := Nat.le_mul_of_pos_right twoS hL1
          omega
        by_cases hhalf : 2 * M ≤ twoS * L
        · exact hchain (M - 1 - twoS) M (by omega) hhalf
        · rw [card_restrictedOccupancy2D_spinFlip twoS L M hMle]
          apply hchain (M - 1 - twoS) (twoS * L - M)
          · omega
          · omega
    · rw [sub_zero]
      exact Nat.cast_nonneg _

/-- Unimodality of `c_s(L; M)` up to half-filling (`2M ≤ 2sL`). -/
theorem card_restrictedOccupancy2D_mono_half (twoS L M : ℕ)
    (hM1 : 1 ≤ M) (hM2 : 2 * M ≤ twoS * L) :
    Fintype.card (restrictedOccupancy2D twoS L (M - 1)) ≤
      Fintype.card (restrictedOccupancy2D twoS L M) :=
  card_restrictedOccupancy2D_mono_half_aux twoS L M hM1 hM2

/-- Nonnegativity of `rank1UntwistedCount` for `1 ≤ M` and `2M ≤ 2sL`. -/
theorem rank1UntwistedCount_nonneg (twoS L M : ℕ)
    (hM1 : 1 ≤ M) (hM2 : 2 * M ≤ twoS * L) :
    0 ≤ rank1UntwistedCount twoS L M := by
  rw [rank1UntwistedCount, sub_nonneg, Int.ofNat_le]
  exact card_restrictedOccupancy2D_mono_half twoS L M hM1 hM2

/-- Stabilization of `rank1UntwistedCount` for `2 ≤ L`, `1 ≤ M ≤ 2s`: `choose (L + M - 2) M`. -/
theorem rank1UntwistedCount_of_le (twoS L M : ℕ)
    (hL : 2 ≤ L) (hM1 : 1 ≤ M) (hM2 : M ≤ twoS) :
    rank1UntwistedCount twoS L M = (Nat.choose (L + M - 2) M : ℤ) := by
  rw [rank1UntwistedCount]
  rw [card_restrictedOccupancy2D_of_le twoS L M hM2]
  rw [card_restrictedOccupancy2D_of_le twoS L (M - 1) (le_trans (Nat.sub_le _ _) hM2)]
  have hL' : L - 2 + 2 = L := Nat.sub_add_cancel hL
  have hM' : M - 1 + 1 = M := Nat.sub_add_cancel hM1
  have h1 : L + M - 1 = (L + M - 2) + 1 := by omega
  have h2 : L + (M - 1) - 1 = L + M - 2 := by omega
  rw [h1, h2]
  conv_lhs =>
    lhs
    rw [← hM', Nat.choose_succ_succ, Nat.succ_eq_add_one, hM']
  push_cast
  ring

/-! ## Part 1B: 3D Restricted Occupancy, SSYT Bijection & Seiberg/Weyl Duality -/

/-- 3D restricted occupancy configurations for `SU(r + 1)` spin-`s` chain of length `L`. -/
def restrictedOccupancy3D (twoS L r : ℕ) (M : Fin r → ℕ) : Type :=
  { n : Fin r → Fin L → ℕ //
      (∀ a α, n a α ≤ twoS) ∧
      (∀ α, Antitone (fun a => n a α)) ∧
      (∀ a, ∑ α, n a α = M a) }

instance (twoS L r : ℕ) (M : Fin r → ℕ) : DecidableEq (restrictedOccupancy3D twoS L r M) :=
  inferInstanceAs (DecidableEq { n : Fin r → Fin L → ℕ //
      (∀ a α, n a α ≤ twoS) ∧
      (∀ α, Antitone (fun a => n a α)) ∧
      (∀ a, ∑ α, n a α = M a) })

private def restrictedOccupancy3DEquivFin (twoS L r : ℕ) (M : Fin r → ℕ) :
    restrictedOccupancy3D twoS L r M ≃
      { n : Fin r → Fin L → Fin (twoS + 1) //
        (∀ α, Antitone (fun a => n a α)) ∧ (∀ a, ∑ α, (n a α : ℕ) = M a) } where
  toFun n :=
    ⟨fun a α => ⟨n.1 a α, Nat.lt_succ_of_le (n.2.1 a α)⟩,
      ⟨fun α a b hab => n.2.2.1 α hab, fun a => by simpa using n.2.2.2 a⟩⟩
  invFun n :=
    ⟨fun a α => (n.1 a α).val,
      ⟨fun a α => Nat.le_of_lt_succ (n.1 a α).isLt,
        fun α a b hab => n.2.1 α hab,
        n.2.2⟩⟩
  left_inv _ := Subtype.ext (funext fun _ => funext fun _ => rfl)
  right_inv _ := Subtype.ext (funext fun _ => funext fun _ => rfl)

instance (twoS L r : ℕ) (M : Fin r → ℕ) : Fintype (restrictedOccupancy3D twoS L r M) :=
  Fintype.ofEquiv _ (restrictedOccupancy3DEquivFin twoS L r M).symm

/-- Canonical empty witness for `restrictedOccupancy3D`. -/
def canonicalRestrictedOccupancy3D : restrictedOccupancy3D 0 0 0 Fin.elim0 :=
  ⟨Fin.elim0, fun a => Fin.elim0 a, fun α => Fin.elim0 α, fun a => Fin.elim0 a⟩

/-- Equivalence between `Antitone` + uniform `≤ 2s` and step-by-step nesting inequalities. -/
theorem mem_restrictedOccupancy3D_iff_succ (twoS L r : ℕ) (M : Fin r → ℕ)
    (n : Fin r → Fin L → ℕ) :
    ((∀ a α, n a α ≤ twoS) ∧ (∀ α, Antitone (fun a => n a α)) ∧ (∀ a, ∑ α, n a α = M a)) ↔
      (∀ (hr : 0 < r) α, n ⟨0, hr⟩ α ≤ twoS) ∧
      (∀ (a : ℕ) (ha : a + 1 < r) α, n ⟨a + 1, ha⟩ α ≤ n ⟨a, Nat.lt_of_succ_lt ha⟩ α) ∧
      (∀ a, ∑ α, n a α = M a) := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun hr α => h1 ⟨0, hr⟩ α, fun a ha α => ?_, h3⟩
    exact h2 α (Nat.le_of_lt (Nat.lt_succ_self a))
  · rintro ⟨h1, h2, h3⟩
    rcases r with _ | r
    · exact ⟨fun a => Fin.elim0 a, fun _ a => Fin.elim0 a, h3⟩
    · have hant : ∀ α, Antitone (fun a => n a α) := by
        intro α
        change Antitone (fun a : Fin (r + 1) => n a α)
        rw [Fin.antitone_iff_succ_le]
        intro a
        exact h2 a.val (Nat.succ_lt_succ a.isLt) α
      refine ⟨fun a α => ?_, hant, h3⟩
      exact le_trans (hant α (Fin.zero_le a)) (h1 (Nat.succ_pos r) α)

/-- Single-site profile of column lengths `(n^(1)_α, ..., n^(r)_α)` bounded by `2s`. -/
def SiteProfile (twoS r : ℕ) : Type :=
  { p : Fin r → ℕ // (∀ a, p a ≤ twoS) ∧ Antitone p }

instance (twoS r : ℕ) : DecidableEq (SiteProfile twoS r) :=
  inferInstanceAs (DecidableEq { p : Fin r → ℕ // (∀ a, p a ≤ twoS) ∧ Antitone p })

private def siteProfileEquivFin (twoS r : ℕ) :
    SiteProfile twoS r ≃ { p : Fin r → Fin (twoS + 1) // Antitone p } where
  toFun p := ⟨fun a => ⟨p.1 a, Nat.lt_succ_of_le (p.2.1 a)⟩, fun _ _ h => p.2.2 h⟩
  invFun p := ⟨fun a => (p.1 a).val, fun a => Nat.le_of_lt_succ (p.1 a).isLt, fun _ _ h => p.2 h⟩
  left_inv _ := Subtype.ext (funext fun _ => rfl)
  right_inv _ := Subtype.ext (funext fun _ => rfl)

instance (twoS r : ℕ) : Fintype (SiteProfile twoS r) :=
  Fintype.ofEquiv _ (siteProfileEquivFin twoS r).symm

/-- Canonical empty witness for `SiteProfile`. -/
def canonicalSiteProfile : SiteProfile 0 0 :=
  ⟨Fin.elim0, fun a => Fin.elim0 a, fun a => Fin.elim0 a⟩

private lemma card_filter_lt_val {m : ℕ} (k : Fin m) :
    (Finset.univ.filter (fun i : Fin m => i.val < k.val)).card = k.val := by
  have heq : Finset.univ.filter (fun i : Fin m => i.val < k.val) =
      (Finset.range k.val).attach.map
        ⟨fun x => ⟨x.1, lt_trans (Finset.mem_range.mp x.2) k.isLt⟩,
          fun x y h => Subtype.ext (by simpa using congrArg Fin.val h)⟩ := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Finset.mem_attach, Subtype.exists, Finset.mem_range]
    constructor
    · intro hi
      exact ⟨i.val, hi, by ext; rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact hj
  rw [heq, Finset.card_map, Finset.card_attach, Finset.card_range]

private lemma card_filter_le_val {m : ℕ} (k : Fin m) :
    (Finset.univ.filter (fun i : Fin m => i.val ≤ k.val)).card = k.val + 1 := by
  have heq : Finset.univ.filter (fun i : Fin m => i.val ≤ k.val) =
      (Finset.range (k.val + 1)).attach.map
        ⟨fun x => ⟨x.1, lt_of_lt_of_le (Finset.mem_range.mp x.2) k.isLt⟩,
          fun x y h => Subtype.ext (by simpa using congrArg Fin.val h)⟩ := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Finset.mem_attach, Subtype.exists, Finset.mem_range]
    constructor
    · intro hi
      exact ⟨i.val, Nat.lt_succ_of_le hi, by ext; rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact Nat.le_of_lt_succ hj
  rw [heq, Finset.card_map, Finset.card_attach, Finset.card_range]

private lemma antitone_card_filter_lt_iff {m : ℕ} {f : Fin m → ℕ} (hf : Antitone f)
    (k : Fin m) (x : ℕ) :
    k.val < (Finset.univ.filter (fun i : Fin m => x < f i)).card ↔ x < f k := by
  constructor
  · intro hlt
    by_contra hle
    have hfk : f k ≤ x := not_lt.mp hle
    have hsub : Finset.univ.filter (fun i : Fin m => x < f i) ⊆
        Finset.univ.filter (fun i : Fin m => i.val < k.val) := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      by_contra hik
      have hki : k ≤ i := Fin.le_def.mpr (not_lt.mp hik)
      have := hf hki
      omega
    have hcard := (Finset.card_le_card hsub).trans_eq (card_filter_lt_val k)
    omega
  · intro hx
    have hsub : Finset.univ.filter (fun i : Fin m => i.val ≤ k.val) ⊆
        Finset.univ.filter (fun i : Fin m => x < f i) := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      have hik : i ≤ k := Fin.le_def.mpr hi
      exact lt_of_lt_of_le hx (hf hik)
    have hcard := (card_filter_le_val k).symm.trans_le (Finset.card_le_card hsub)
    omega

private lemma card_filter_lt_nat_eq {m : ℕ} (y : ℕ) (hy : y ≤ m) :
    (Finset.univ.filter (fun i : Fin m => i.val < y)).card = y := by
  have heq : Finset.univ.filter (fun i : Fin m => i.val < y) =
      (Finset.range y).attach.map
        ⟨fun x => ⟨x.1, lt_of_lt_of_le (Finset.mem_range.mp x.2) hy⟩,
          fun x y' h => Subtype.ext (by simpa using congrArg Fin.val h)⟩ := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Finset.mem_attach, Subtype.exists, Finset.mem_range]
    constructor
    · intro hi
      exact ⟨i.val, hi, by ext; rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact hj
  rw [heq, Finset.card_map, Finset.card_attach, Finset.card_range]

/-- Conjugate-partition Galois bijection: `SiteProfile twoS r` ↔ antitone SSYT of length `2s`. -/
def ssytSiteAntitoneEquiv (twoS r : ℕ) :
    SiteProfile twoS r ≃ { h : Fin twoS → Fin (r + 1) // Antitone h } where
  toFun p :=
    ⟨fun i =>
      ⟨(Finset.univ.filter (fun a : Fin r => i.val < p.1 a)).card,
        Nat.lt_succ_of_le ((Finset.card_filter_le _ _).trans (by simp))⟩,
      fun i j hij => by
        change (Finset.univ.filter (fun a : Fin r => j.val < p.1 a)).card ≤
          (Finset.univ.filter (fun a : Fin r => i.val < p.1 a)).card
        apply Finset.card_le_card
        intro a ha
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
        exact lt_of_le_of_lt hij ha⟩
  invFun h :=
    ⟨fun a => (Finset.univ.filter (fun i : Fin twoS => a.val < (h.1 i).val)).card,
      fun a => (Finset.card_filter_le _ _).trans (by simp),
      fun a b hab => by
        apply Finset.card_le_card
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        exact lt_of_le_of_lt hab hi⟩
  left_inv p := Subtype.ext (funext fun a => by
    have hset :
        Finset.univ.filter (fun i : Fin twoS =>
          a.val < (Finset.univ.filter (fun b : Fin r => i.val < p.1 b)).card) =
          Finset.univ.filter (fun i : Fin twoS => i.val < p.1 a) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact antitone_card_filter_lt_iff p.2.2 a i.val
    dsimp only
    rw [hset, card_filter_lt_nat_eq (p.1 a) (p.2.1 a)])
  right_inv h := by
    ext i
    have hset :
        Finset.univ.filter (fun a : Fin r =>
          i.val < (Finset.univ.filter (fun j : Fin twoS => a.val < (h.1 j).val)).card) =
          Finset.univ.filter (fun a : Fin r => a.val < (h.1 i).val) := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hval : Antitone (fun j : Fin twoS => (h.1 j).val) := fun _ _ hle => h.2 hle
      exact antitone_card_filter_lt_iff hval i a.val
    dsimp only
    rw [hset, card_filter_lt_nat_eq (h.1 i).val (Nat.le_of_lt_succ (h.1 i).isLt)]

/-- Bijection between `SiteProfile twoS r` and monotone single-row SSYTs `Fin twoS → Fin (r + 1)`. -/
def ssytSiteMonotoneEquiv (twoS r : ℕ) :
    SiteProfile twoS r ≃ { h : Fin twoS → Fin (r + 1) // Monotone h } :=
  (ssytSiteAntitoneEquiv twoS r).trans
    { toFun := fun h => ⟨fun i => h.1 i.rev, fun _ _ hij => h.2 (Fin.rev_le_rev.mpr hij)⟩
      invFun := fun h => ⟨fun i => h.1 i.rev, fun _ _ hij => h.2 (Fin.rev_le_rev.mpr hij)⟩
      left_inv := fun h => by ext i; simp
      right_inv := fun h => by ext i; simp }

/-- Pad a row `f : Fin r → ℕ` with boundary values `f(-1) = top` and `f(r) = 0`. -/
def padRow (top : ℕ) {r : ℕ} (f : Fin r → ℕ) (k : ℕ) : ℕ :=
  if k = 0 then top else if h : k - 1 < r then f ⟨k - 1, h⟩ else 0

private lemma padRow_antitone {top r : ℕ} {f : Fin r → ℕ}
    (hf1 : ∀ a, f a ≤ top) (hf2 : Antitone f) {j k : ℕ} (hjk : j ≤ k) :
    padRow top f k ≤ padRow top f j := by
  unfold padRow
  by_cases hj0 : j = 0
  · subst hj0
    simp only [↓reduceIte]
    split_ifs with hk0 hkr
    · exact le_rfl
    · exact hf1 ⟨k - 1, hkr⟩
    · exact Nat.zero_le top
  · have hk0 : k ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le (Nat.pos_of_ne_zero hj0) hjk)
    simp only [hj0, hk0, ↓reduceIte]
    split_ifs with hkr hjr
    · exact hf2 (Fin.le_def.mpr (Nat.sub_le_sub_right hjk 1))
    · exact absurd (lt_of_le_of_lt (Nat.sub_le_sub_right hjk 1) hkr) hjr
    · exact Nat.zero_le _
    · exact le_rfl

private lemma padRow_last {top r : ℕ} (f : Fin r → ℕ) : padRow top f (r + 1) = 0 := by
  unfold padRow
  simp

private lemma padRow_zero {top r : ℕ} (f : Fin r → ℕ) : padRow top f 0 = top := by
  unfold padRow
  simp

private def siteProfileEquivNatSum (twoS r : ℕ) :
    SiteProfile twoS r ≃ { c : Fin (r + 1) → ℕ // ∑ k, c k = twoS } where
  toFun p :=
    ⟨fun k => padRow twoS p.1 k.val - padRow twoS p.1 (k.val + 1), by
      let f : ℕ → ℕ := fun k => padRow twoS p.1 k - padRow twoS p.1 (k + 1)
      change ∑ k : Fin (r + 1), f k.val = twoS
      rw [Fin.sum_univ_eq_sum_range]
      have htel : ∀ m ≤ r + 1,
          (∑ k ∈ Finset.range m, f k) = twoS - padRow twoS p.1 m := by
        intro m hm
        induction m with
        | zero => simp [padRow_zero]
        | succ m ih =>
          rw [Finset.sum_range_succ, ih (Nat.le_of_succ_le hm)]
          have h1 : padRow twoS p.1 (m + 1) ≤ padRow twoS p.1 m :=
            padRow_antitone p.2.1 p.2.2 (Nat.le_succ m)
          have h2 : padRow twoS p.1 m ≤ twoS := by
            simpa [padRow_zero] using padRow_antitone p.2.1 p.2.2 (Nat.zero_le m)
          dsimp only [f]
          omega
      rw [htel (r + 1) le_rfl, padRow_last]
      simp⟩
  invFun c :=
    ⟨fun a => ∑ k : Fin (r + 1), if a.val < k.val then c.1 k else 0,
      fun a => by
        calc
          (∑ k : Fin (r + 1), if a.val < k.val then c.1 k else 0)
              ≤ ∑ k : Fin (r + 1), c.1 k :=
            Finset.sum_le_sum fun k _ => by split_ifs <;> simp
          _ = twoS := c.2,
      fun a b hab => by
        refine Finset.sum_le_sum fun k _ => ?_
        by_cases hb : b.val < k.val
        · have ha : a.val < k.val := lt_of_le_of_lt hab hb
          simp [ha, hb]
        · simp [hb]⟩
  left_inv p := Subtype.ext (funext fun a => by
    let f : ℕ → ℕ := fun k => padRow twoS p.1 k - padRow twoS p.1 (k + 1)
    change (∑ k : Fin (r + 1), if a.val < k.val then f k.val else 0) = p.1 a
    have hsum :
        (∑ k : Fin (r + 1), if a.val < k.val then f k.val else 0) =
          ∑ k ∈ Finset.Ico (a.val + 1) (r + 1), f k := by
      rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => if a.val < k then f k else 0),
        ← Finset.sum_filter]
      refine Finset.sum_congr ?_ (fun _ _ => rfl)
      ext k
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      omega
    rw [hsum]
    have htel : ∀ m, a.val + 1 ≤ m → m ≤ r + 1 →
        ∑ k ∈ Finset.Ico (a.val + 1) m, f k =
          padRow twoS p.1 (a.val + 1) - padRow twoS p.1 m := by
      intro m hm1 hm2
      induction m with
      | zero => omega
      | succ m ih =>
        rcases eq_or_lt_of_le hm1 with hEq | hLt
        · have hle : m + 1 ≤ a.val + 1 := by omega
          rw [Finset.Ico_eq_empty_of_le hle, Finset.sum_empty]
          have hEq' : m + 1 = a.val + 1 := by omega
          rw [hEq', Nat.sub_self]
        · have hm1' : a.val + 1 ≤ m := Nat.le_of_lt_succ hLt
          have hsplit : Finset.Ico (a.val + 1) (m + 1) =
              insert m (Finset.Ico (a.val + 1) m) := by
            ext k
            simp only [Finset.mem_Ico, Finset.mem_insert]
            omega
          rw [hsplit, Finset.sum_insert (by simp), ih hm1' (Nat.le_of_succ_le hm2)]
          have h1 : padRow twoS p.1 (m + 1) ≤ padRow twoS p.1 m :=
            padRow_antitone p.2.1 p.2.2 (Nat.le_succ m)
          have h2 : padRow twoS p.1 m ≤ padRow twoS p.1 (a.val + 1) :=
            padRow_antitone p.2.1 p.2.2 hm1'
          dsimp only [f]
          omega
    rw [htel (r + 1) (Nat.le_succ_of_le (Nat.succ_le_of_lt a.isLt)) le_rfl,
      padRow_last, Nat.sub_zero]
    unfold padRow
    simp [a.isLt])
  right_inv c := by
    ext k
    have hpad : ∀ (m : ℕ) (hm : m ≤ r + 1),
        padRow twoS (fun a : Fin r =>
          ∑ j : Fin (r + 1), if a.val < j.val then c.1 j else 0) m =
          ∑ j : Fin (r + 1), if m ≤ j.val then c.1 j else 0 := by
      intro m hm
      rcases m with _ | m
      · rw [padRow_zero]
        have hsum : ∑ j : Fin (r + 1), (if 0 ≤ j.val then c.1 j else 0) = ∑ j, c.1 j := by
          simp
        rw [hsum, c.2]
      · unfold padRow
        simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
          Nat.add_sub_cancel]
        split_ifs with hmr
        · refine Finset.sum_congr rfl fun j _ => ?_
          have hiff : m < j.val ↔ m + 1 ≤ j.val := by omega
          by_cases hmj : m < j.val
          · simp [hmj, hiff.mp hmj]
          · simp [hmj, mt hiff.mpr hmj]
        · have hm_eq : m + 1 = r + 1 := by omega
          symm
          refine Finset.sum_eq_zero fun j _ => ?_
          have hj : ¬ (m + 1 ≤ j.val) := by omega
          simp [hj]
    dsimp only
    rw [hpad k.val (Nat.le_of_lt k.isLt), hpad (k.val + 1) k.isLt]
    have hsplit : (∑ j : Fin (r + 1), if k.val ≤ j.val then c.1 j else 0) =
        c.1 k + ∑ j : Fin (r + 1), if k.val + 1 ≤ j.val then c.1 j else 0 := by
      have hpoint : ∀ j : Fin (r + 1),
          (if k.val ≤ j.val then c.1 j else 0) =
            (if j = k then c.1 k else 0) + (if k.val + 1 ≤ j.val then c.1 j else 0) := by
        intro j
        by_cases hjk : j = k
        · subst hjk
          simp
        · have hne : j.val ≠ k.val := fun h => hjk (Fin.ext h)
          by_cases hle : k.val ≤ j.val
          · have hlt : k.val + 1 ≤ j.val := by omega
            simp [hjk, hle, hlt]
          · have hlt : ¬ (k.val + 1 ≤ j.val) := by omega
            simp [hjk, hle, hlt]
      simp_rw [hpoint, Finset.sum_add_distrib]
      simp
    rw [hsplit]
    omega

/-- Stars-and-bars bijection `SiteProfile twoS r ≃ Sym (Fin (r + 1)) twoS`. -/
noncomputable def siteProfileEquivSym (twoS r : ℕ) :
    SiteProfile twoS r ≃ Sym (Fin (r + 1)) twoS :=
  (siteProfileEquivNatSum twoS r).trans (Sym.equivNatSumOfFintype (Fin (r + 1)) twoS).symm

/-- Number of single-site profiles is `choose (2s + r) r`. -/
theorem card_siteProfile (twoS r : ℕ) :
    Fintype.card (SiteProfile twoS r) = Nat.choose (twoS + r) r := by
  classical
  rw [Fintype.card_congr (siteProfileEquivSym twoS r), Sym.card_sym_eq_choose, Fintype.card_fin]
  have hsum : r + 1 + twoS - 1 = twoS + r := by omega
  rw [hsum]
  apply Nat.choose_symm_of_eq_add
  omega

/-- Number of single-row SSYTs of length `2s` with entries in `{0, ..., r}` is `choose (2s + r) r`. -/
theorem card_ssytMonotone (twoS r : ℕ) :
    Fintype.card { h : Fin twoS → Fin (r + 1) // Monotone h } = Nat.choose (twoS + r) r := by
  rw [← Fintype.card_congr (ssytSiteMonotoneEquiv twoS r), card_siteProfile]

/-- Valid total magnon vectors `0 ≤ M_r ≤ ⋯ ≤ M_1 ≤ 2sL`. -/
def ValidMagnonVec (twoS L r : ℕ) : Type :=
  { M : Fin r → ℕ // (∀ a, M a ≤ twoS * L) ∧ Antitone M }

instance (twoS L r : ℕ) : DecidableEq (ValidMagnonVec twoS L r) :=
  inferInstanceAs (DecidableEq { M : Fin r → ℕ // (∀ a, M a ≤ twoS * L) ∧ Antitone M })

private def validMagnonVecEquivFin (twoS L r : ℕ) :
    ValidMagnonVec twoS L r ≃ { M : Fin r → Fin (twoS * L + 1) // Antitone M } where
  toFun M := ⟨fun a => ⟨M.1 a, Nat.lt_succ_of_le (M.2.1 a)⟩, fun _ _ h => M.2.2 h⟩
  invFun M := ⟨fun a => (M.1 a).val, fun a => Nat.le_of_lt_succ (M.1 a).isLt, fun _ _ h => M.2 h⟩
  left_inv _ := Subtype.ext (funext fun _ => rfl)
  right_inv _ := Subtype.ext (funext fun _ => rfl)

instance (twoS L r : ℕ) : Fintype (ValidMagnonVec twoS L r) :=
  Fintype.ofEquiv _ (validMagnonVecEquivFin twoS L r).symm

/-- Canonical empty witness for `ValidMagnonVec`. -/
def canonicalValidMagnonVec : ValidMagnonVec 0 0 0 :=
  ⟨Fin.elim0, fun a => Fin.elim0 a, fun a => Fin.elim0 a⟩

/-- Total 3D restricted-occupancy configurations decompose over sites into `Fin L → SiteProfile`. -/
def restrictedOccupancy3D_sigma_equiv (twoS L r : ℕ) :
    (M : ValidMagnonVec twoS L r) × restrictedOccupancy3D twoS L r M.1 ≃
      (Fin L → SiteProfile twoS r) where
  toFun x α := ⟨fun a => x.2.1 a α, fun a => x.2.2.1 a α, fun _ _ h => x.2.2.2.1 α h⟩
  invFun f :=
    let Mval : Fin r → ℕ := fun a => ∑ α : Fin L, (f α).1 a
    have hM1 : ∀ a, Mval a ≤ twoS * L := by
      intro a
      calc
        ∑ α : Fin L, (f α).1 a ≤ ∑ _α : Fin L, twoS :=
          Finset.sum_le_sum fun α _ => (f α).2.1 a
        _ = twoS * L := by
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_comm]
    have hM2 : Antitone Mval := fun a b hab =>
      Finset.sum_le_sum fun α _ => (f α).2.2 hab
    ⟨⟨Mval, hM1, hM2⟩, ⟨fun a α => (f α).1 a,
      fun a α => (f α).2.1 a, fun α a b hab => (f α).2.2 hab, fun _ => rfl⟩⟩
  left_inv x := by
    rcases x with ⟨⟨M, hM1, hM2⟩, ⟨n, hn1, hn2, hn3⟩⟩
    have hMeq : (fun a => ∑ α : Fin L, n a α) = M := funext hn3
    dsimp only
    subst hMeq
    rfl
  right_inv f := funext fun _ => Subtype.ext (funext fun _ => rfl)

/-- Total 3D restricted-occupancy configurations correspond to `L`-tuples of single-row SSYTs. -/
def restrictedOccupancy3D_sigma_ssytEquiv (twoS L r : ℕ) :
    (M : ValidMagnonVec twoS L r) × restrictedOccupancy3D twoS L r M.1 ≃
      (Fin L → { h : Fin twoS → Fin (r + 1) // Monotone h }) :=
  (restrictedOccupancy3D_sigma_equiv twoS L r).trans
    (Equiv.piCongrRight fun _ => ssytSiteMonotoneEquiv twoS r)

/-- Eq. (9) of Shu et al.: `∑_{0 ≤ M_r ≤ ⋯ ≤ M_1 ≤ 2sL} c_s(L; M_1, ..., M_r) = choose (2s + r) r ^ L`. -/
theorem sum_card_restrictedOccupancy3D (twoS L r : ℕ) :
    ∑ M : ValidMagnonVec twoS L r, Fintype.card (restrictedOccupancy3D twoS L r M.1) =
      (Nat.choose (twoS + r) r) ^ L := by
  have hcard := Fintype.card_congr (restrictedOccupancy3D_sigma_equiv twoS L r)
  rw [Fintype.card_sigma, Fintype.card_pi_const, card_siteProfile] at hcard
  simpa [Fintype.card_fin] using hcard

/-- Eq. (10) of Shu et al.: Seiberg/Weyl reflection of magnon vector `M` at node `a`. -/
def weylReflectM (twoS L r : ℕ) (M : Fin r → ℕ) (a : Fin r) : Fin r → ℕ :=
  fun b => if b = a then padRow (twoS * L) M a.val + padRow (twoS * L) M (a.val + 2) - M a
    else M b

/-- Eq. (11) of Shu et al.: Seiberg/Weyl reflection of configuration `n` at node `a`. -/
def weylReflectFun (twoS L r : ℕ) (n : Fin r → Fin L → ℕ) (a : Fin r) : Fin r → Fin L → ℕ :=
  fun b α =>
    if b = a then
      padRow twoS (fun c => n c α) a.val + padRow twoS (fun c => n c α) (a.val + 2) - n a α
    else n b α

/-- `weylReflectM` preserves `ValidMagnonVec` (`Antitone` and bounded by `2sL`). -/
theorem weylReflectM_valid (twoS L r : ℕ) (M : ValidMagnonVec twoS L r) (a : Fin r) :
    (∀ b, weylReflectM twoS L r M.1 a b ≤ twoS * L) ∧
      Antitone (weylReflectM twoS L r M.1 a) := by
  have hprev : M.1 a ≤ padRow (twoS * L) M.1 a.val := by
    have := padRow_antitone M.2.1 M.2.2 (Nat.le_succ a.val)
    simpa [padRow, a.isLt] using this
  have hnext : padRow (twoS * L) M.1 (a.val + 2) ≤ M.1 a := by
    have := padRow_antitone M.2.1 M.2.2 (Nat.le_succ (a.val + 1))
    simpa [padRow, a.isLt] using this
  have hprev_le : padRow (twoS * L) M.1 a.val ≤ twoS * L := by
    simpa [padRow_zero] using padRow_antitone M.2.1 M.2.2 (Nat.zero_le a.val)
  constructor
  · intro b
    unfold weylReflectM
    split_ifs with hb
    · omega
    · exact M.2.1 b
  · rcases r with _ | r
    · exact fun a => Fin.elim0 a
    · change Antitone (weylReflectM twoS L (r + 1) M.1 a)
      rw [Fin.antitone_iff_succ_le]
      intro b
      unfold weylReflectM
      have hstep : M.1 b.succ ≤ M.1 b.castSucc := M.2.2 (Nat.le_of_lt (Nat.lt_succ_self b.val))
      by_cases h1 : b.succ = a
      · have h2 : b.castSucc ≠ a := fun h => by
          have := congrArg Fin.val (h1.trans h.symm)
          simp at this
        simp only [h1, ↓reduceIte, h2]
        have hpad : padRow (twoS * L) M.1 a.val = M.1 b.castSucc := by
          have ha : a.val = b.val + 1 := by simpa using congrArg Fin.val h1.symm
          have hlt : b.val < r + 1 := b.castSucc.isLt
          unfold padRow
          rw [ha]
          simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
            Nat.add_sub_cancel, hlt, ↓reduceDIte]
          exact congrArg M.1 (Fin.ext rfl)
        have hle : M.1 a ≤ M.1 b.castSucc := by rw [← h1]; exact hstep
        omega
      · by_cases h2 : b.castSucc = a
        · simp only [h1, ↓reduceIte, h2]
          have hpad : padRow (twoS * L) M.1 (a.val + 2) = M.1 b.succ := by
            have ha : a.val = b.val := by simpa using congrArg Fin.val h2.symm
            unfold padRow
            rw [ha]
            have hne0 : b.val + 2 ≠ 0 := by omega
            have hlt : b.val + 2 - 1 < r + 1 := by simpa using b.succ.isLt
            simp only [hne0, ↓reduceIte, hlt, ↓reduceDIte]
            exact congrArg M.1 (Fin.ext (by simp))
          have hle : M.1 b.succ ≤ M.1 a := by rw [← h2]; exact hstep
          omega
        · simp only [h1, ↓reduceIte, h2]
          exact hstep

/-- `weylReflectM` is an involution whenever `M a ≤ M_{a-1} + M_{a+1}`. -/
theorem weylReflectM_involutive (twoS L r : ℕ) (M : Fin r → ℕ) (a : Fin r)
    (hMa : M a ≤ padRow (twoS * L) M a.val + padRow (twoS * L) M (a.val + 2)) :
    weylReflectM twoS L r (weylReflectM twoS L r M a) a = M := by
  have hpad1 : padRow (twoS * L) (weylReflectM twoS L r M a) a.val = padRow (twoS * L) M a.val := by
    unfold padRow
    split_ifs with h0 hr
    · rfl
    · unfold weylReflectM
      have hne : (⟨a.val - 1, hr⟩ : Fin r) ≠ a := by
        intro heq
        have hval := congrArg Fin.val heq
        dsimp only at hval
        omega
      simp [hne]
    · rfl
  have hpad2 : padRow (twoS * L) (weylReflectM twoS L r M a) (a.val + 2) =
      padRow (twoS * L) M (a.val + 2) := by
    by_cases hr : a.val + 1 < r
    · have hne : (⟨a.val + 1, hr⟩ : Fin r) ≠ a := by
        intro heq
        have hval := congrArg Fin.val heq
        dsimp only at hval
        omega
      have hne' : a.val + 2 ≠ 0 := by omega
      have hr' : a.val + 2 - 1 < r := by omega
      have h1 : padRow (twoS * L) (weylReflectM twoS L r M a) (a.val + 2) =
          weylReflectM twoS L r M a ⟨a.val + 1, hr⟩ := by
        unfold padRow
        simp only [hne', ↓reduceIte, hr', ↓reduceDIte]
        exact congrArg (weylReflectM twoS L r M a) (Fin.ext (by simp))
      have h2 : padRow (twoS * L) M (a.val + 2) = M ⟨a.val + 1, hr⟩ := by
        unfold padRow
        simp only [hne', ↓reduceIte, hr', ↓reduceDIte]
        exact congrArg M (Fin.ext (by simp))
      rw [h1, h2, weylReflectM, if_neg hne]
    · have hne' : a.val + 2 ≠ 0 := by omega
      have hnr : ¬ (a.val + 2 - 1 < r) := by omega
      have h1 : padRow (twoS * L) (weylReflectM twoS L r M a) (a.val + 2) = 0 := by
        unfold padRow; simp only [hne', ↓reduceIte, hnr, ↓reduceDIte]
      have h2 : padRow (twoS * L) M (a.val + 2) = 0 := by
        unfold padRow; simp only [hne', ↓reduceIte, hnr, ↓reduceDIte]
      rw [h1, h2]
  ext b
  rw [weylReflectM]
  split_ifs with hb
  · rw [hb, hpad1, hpad2]
    rw [weylReflectM, if_pos rfl]
    exact Nat.sub_sub_self hMa
  · rw [weylReflectM, if_neg hb]

/-- Eqs. (10)–(11) of Shu et al.: Seiberg/Weyl reflection bijection on 3D restricted occupancy. -/
def weylReflect3DEquiv (twoS L r : ℕ) (M : Fin r → ℕ) (a : Fin r)
    (hMa : M a ≤ padRow (twoS * L) M a.val + padRow (twoS * L) M (a.val + 2)) :
    restrictedOccupancy3D twoS L r M ≃
      restrictedOccupancy3D twoS L r (weylReflectM twoS L r M a) where
  toFun n :=
    have hvalid : ∀ α, (∀ b, weylReflectFun twoS L r n.1 a b α ≤ twoS) ∧
        Antitone (fun b => weylReflectFun twoS L r n.1 a b α) := by
      intro α
      let p : ValidMagnonVec twoS 1 r :=
        ⟨fun b => n.1 b α, fun b => by simpa using n.2.1 b α, n.2.2.1 α⟩
      have hv := weylReflectM_valid twoS 1 r p a
      refine ⟨fun b => ?_, fun b c hbc => ?_⟩
      · simpa [weylReflectM, weylReflectFun, p, mul_one] using hv.1 b
      · simpa [weylReflectM, weylReflectFun, p, mul_one] using hv.2 hbc
    have hsum : ∀ b, ∑ α, weylReflectFun twoS L r n.1 a b α = weylReflectM twoS L r M a b := by
      intro b
      unfold weylReflectFun weylReflectM
      split_ifs with hb
      · have hle : ∀ α, n.1 a α ≤
            padRow twoS (fun c => n.1 c α) a.val +
              padRow twoS (fun c => n.1 c α) (a.val + 2) := by
          intro α
          have := padRow_antitone (fun c => n.2.1 c α) (n.2.2.1 α) (Nat.le_succ a.val)
          have h1 : n.1 a α ≤ padRow twoS (fun c => n.1 c α) a.val := by
            simpa [padRow, a.isLt] using this
          omega
        have hsub :
            ∑ α : Fin L,
              (padRow twoS (fun c => n.1 c α) a.val +
                padRow twoS (fun c => n.1 c α) (a.val + 2) - n.1 a α) +
              ∑ α : Fin L, n.1 a α =
              ∑ α : Fin L, padRow twoS (fun c => n.1 c α) a.val +
                ∑ α : Fin L, padRow twoS (fun c => n.1 c α) (a.val + 2) := by
          rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun α _ => ?_
          rw [Nat.sub_add_cancel (hle α)]
        have hp1 : ∑ α : Fin L, padRow twoS (fun c => n.1 c α) a.val =
            padRow (twoS * L) M a.val := by
          unfold padRow
          split_ifs with h0 hr
          · simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_comm]
          · simp [n.2.2.2 ⟨a.val - 1, hr⟩]
          · simp
        have hp2 : ∑ α : Fin L, padRow twoS (fun c => n.1 c α) (a.val + 2) =
            padRow (twoS * L) M (a.val + 2) := by
          unfold padRow
          have h0 : a.val + 2 ≠ 0 := by omega
          simp only [h0, ↓reduceIte]
          split_ifs with hr
          · exact n.2.2.2 ⟨a.val + 2 - 1, hr⟩
          · simp
        have hna : ∑ α : Fin L, n.1 a α = M a := n.2.2.2 a
        rw [hp1, hp2, hna] at hsub
        exact Nat.eq_sub_of_add_eq hsub
      · exact n.2.2.2 b
    ⟨weylReflectFun twoS L r n.1 a,
      fun b α => (hvalid α).1 b,
      fun α => (hvalid α).2,
      hsum⟩
  invFun n :=
    have hvalid : ∀ α, (∀ b, weylReflectFun twoS L r n.1 a b α ≤ twoS) ∧
        Antitone (fun b => weylReflectFun twoS L r n.1 a b α) := by
      intro α
      let p : ValidMagnonVec twoS 1 r :=
        ⟨fun b => n.1 b α, fun b => by simpa using n.2.1 b α, n.2.2.1 α⟩
      have hv := weylReflectM_valid twoS 1 r p a
      refine ⟨fun b => ?_, fun b c hbc => ?_⟩
      · simpa [weylReflectM, weylReflectFun, p, mul_one] using hv.1 b
      · simpa [weylReflectM, weylReflectFun, p, mul_one] using hv.2 hbc
    have hsum : ∀ b, ∑ α, weylReflectFun twoS L r n.1 a b α = M b := by
      intro b
      unfold weylReflectFun
      split_ifs with hb
      · rw [hb]
        have hle : ∀ α, n.1 a α ≤
            padRow twoS (fun c => n.1 c α) a.val +
              padRow twoS (fun c => n.1 c α) (a.val + 2) := by
          intro α
          have := padRow_antitone (fun c => n.2.1 c α) (n.2.2.1 α) (Nat.le_succ a.val)
          have h1 : n.1 a α ≤ padRow twoS (fun c => n.1 c α) a.val := by
            simpa [padRow, a.isLt] using this
          omega
        have hsub :
            ∑ α : Fin L,
              (padRow twoS (fun c => n.1 c α) a.val +
                padRow twoS (fun c => n.1 c α) (a.val + 2) - n.1 a α) +
              ∑ α : Fin L, n.1 a α =
              ∑ α : Fin L, padRow twoS (fun c => n.1 c α) a.val +
                ∑ α : Fin L, padRow twoS (fun c => n.1 c α) (a.val + 2) := by
          rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun α _ => ?_
          rw [Nat.sub_add_cancel (hle α)]
        have hpad1 : ∑ α : Fin L, padRow twoS (fun c => n.1 c α) a.val =
            padRow (twoS * L) M a.val := by
          unfold padRow
          split_ifs with h0 hr
          · simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_comm]
          · have hne : (⟨a.val - 1, hr⟩ : Fin r) ≠ a := by
              intro heq; have hval := congrArg Fin.val heq; dsimp only at hval; omega
            have hsum' := n.2.2.2 ⟨a.val - 1, hr⟩
            rw [weylReflectM, if_neg hne] at hsum'
            exact hsum'
          · simp
        have hpad2 : ∑ α : Fin L, padRow twoS (fun c => n.1 c α) (a.val + 2) =
            padRow (twoS * L) M (a.val + 2) := by
          unfold padRow
          have h0 : a.val + 2 ≠ 0 := by omega
          simp only [h0, ↓reduceIte]
          split_ifs with hr
          · have hne : (⟨a.val + 2 - 1, hr⟩ : Fin r) ≠ a := by
              intro heq; have hval := congrArg Fin.val heq; dsimp only at hval; omega
            have hsum' := n.2.2.2 ⟨a.val + 2 - 1, hr⟩
            rw [weylReflectM, if_neg hne] at hsum'
            exact hsum'
          · simp
        have hna : ∑ α : Fin L, n.1 a α =
            padRow (twoS * L) M a.val + padRow (twoS * L) M (a.val + 2) - M a := by
          have := n.2.2.2 a
          rw [weylReflectM, if_pos rfl] at this
          exact this
        rw [hpad1, hpad2, hna] at hsub
        have hsub' : ∑ α : Fin L,
            (padRow twoS (fun c => n.1 c α) a.val +
              padRow twoS (fun c => n.1 c α) (a.val + 2) - n.1 a α) =
            padRow (twoS * L) M a.val + padRow (twoS * L) M (a.val + 2) -
              (padRow (twoS * L) M a.val + padRow (twoS * L) M (a.val + 2) - M a) := by
          omega
        rw [hsub', Nat.sub_sub_self hMa]
      · have := n.2.2.2 b
        rw [weylReflectM, if_neg hb] at this
        exact this
    ⟨weylReflectFun twoS L r n.1 a,
      fun b α => (hvalid α).1 b,
      fun α => (hvalid α).2,
      hsum⟩
  left_inv n := Subtype.ext (funext fun b => funext fun α => by
    have hinv : weylReflectM twoS 1 r (weylReflectM twoS 1 r (fun c => n.1 c α) a) a =
        fun c => n.1 c α := by
      apply weylReflectM_involutive
      have h1 : n.1 a α ≤ padRow twoS (fun c => n.1 c α) a.val := by
        have := padRow_antitone (fun c => n.2.1 c α) (n.2.2.1 α) (Nat.le_succ a.val)
        simpa [padRow, a.isLt] using this
      simp only [mul_one]
      omega
    have hfun : ∀ m : Fin r → Fin L → ℕ, (fun b => weylReflectFun twoS L r m a b α) =
        weylReflectM twoS 1 r (fun c => m c α) a := by
      intro m; ext c; simp [weylReflectFun, weylReflectM, mul_one]
    change weylReflectFun twoS L r (weylReflectFun twoS L r n.1 a) a b α = n.1 b α
    rw [congrFun (hfun (weylReflectFun twoS L r n.1 a)) b, hfun n.1, hinv])
  right_inv n := Subtype.ext (funext fun b => funext fun α => by
    have hinv : weylReflectM twoS 1 r (weylReflectM twoS 1 r (fun c => n.1 c α) a) a =
        fun c => n.1 c α := by
      apply weylReflectM_involutive
      have h1 : n.1 a α ≤ padRow twoS (fun c => n.1 c α) a.val := by
        have := padRow_antitone (fun c => n.2.1 c α) (n.2.2.1 α) (Nat.le_succ a.val)
        simpa [padRow, a.isLt] using this
      simp only [mul_one]
      omega
    have hfun : ∀ m : Fin r → Fin L → ℕ, (fun b => weylReflectFun twoS L r m a b α) =
        weylReflectM twoS 1 r (fun c => m c α) a := by
      intro m; ext c; simp [weylReflectFun, weylReflectM, mul_one]
    change weylReflectFun twoS L r (weylReflectFun twoS L r n.1 a) a b α = n.1 b α
    rw [congrFun (hfun (weylReflectFun twoS L r n.1 a)) b, hfun n.1, hinv])

/-- Cardinality invariance under Seiberg/Weyl reflection (Eqs. 10–11). -/
theorem card_restrictedOccupancy3D_weylReflect (twoS L r : ℕ) (M : Fin r → ℕ) (a : Fin r)
    (hMa : M a ≤ padRow (twoS * L) M a.val + padRow (twoS * L) M (a.val + 2)) :
    Fintype.card (restrictedOccupancy3D twoS L r M) =
      Fintype.card (restrictedOccupancy3D twoS L r (weylReflectM twoS L r M a)) :=
  Fintype.card_congr (weylReflect3DEquiv twoS L r M a hMa)

/-- Rank-1 (`r = 1`) specialization of 3D restricted occupancy recovers 2D restricted occupancy. -/
def restrictedOccupancy3D_one_equiv_2D (twoS L : ℕ) (M : Fin 1 → ℕ) :
    restrictedOccupancy3D twoS L 1 M ≃ restrictedOccupancy2D twoS L (M 0) where
  toFun n := ⟨n.1 0, fun α => n.2.1 0 α, n.2.2.2 0⟩
  invFun n :=
    ⟨fun _ => n.1,
      fun _ α => n.2.1 α,
      fun _ _ _ _ => le_rfl,
      fun a => by fin_cases a; exact n.2.2⟩
  left_inv n := Subtype.ext (funext fun a => funext fun α => by fin_cases a; rfl)
  right_inv _ := Subtype.ext (funext fun _ => rfl)

/-! ## Part 2A: Kondo Model Bethe-State Counting (Eqs. 16–17) -/

/-- Eq. (16) of Shu et al.: `c_s^K(L; M) = ∑_{i=0}^{2s} choose L (M - i)` (guarded by `i ≤ M`). -/
def kondoCount (twoS L M : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (twoS + 1), if i ≤ M then Nat.choose L (M - i) else 0

/-- For `M > L + 2s`, `kondoCount twoS L M = 0`. -/
theorem kondoCount_eq_zero_of_lt (twoS L M : ℕ) (hM : L + twoS < M) :
    kondoCount twoS L M = 0 := by
  unfold kondoCount
  refine Finset.sum_eq_zero fun i hi => ?_
  have hi_le : i ≤ twoS := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  split_ifs with him
  · have hlt : L < M - i := Nat.lt_sub_of_add_lt (lt_of_le_of_lt (Nat.add_le_add_left hi_le L) hM)
    exact Nat.choose_eq_zero_of_lt hlt
  · rfl

/-- Total number of Kondo states across `M = 0, ..., L + 2s` is `2^L * (2s + 1)`. -/
theorem sum_kondoCount (twoS L : ℕ) :
    ∑ M ∈ Finset.range (L + twoS + 1), kondoCount twoS L M = 2 ^ L * (twoS + 1) := by
  unfold kondoCount
  rw [Finset.sum_comm]
  have hinner : ∀ i ∈ Finset.range (twoS + 1),
      (∑ M ∈ Finset.range (L + twoS + 1), if i ≤ M then Nat.choose L (M - i) else 0) =
        2 ^ L := by
    intro i hi
    have hi_le : i ≤ twoS := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hfilt :
        (∑ M ∈ Finset.range (L + twoS + 1), if i ≤ M then Nat.choose L (M - i) else 0) =
          ∑ M ∈ Finset.Ico i (L + twoS + 1), Nat.choose L (M - i) := by
      rw [← Finset.sum_filter]
      refine Finset.sum_congr ?_ (fun _ _ => rfl)
      ext M
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      omega
    rw [hfilt, Finset.sum_Ico_eq_sum_range]
    have hadd : ∀ k, i + k - i = k := fun k => Nat.add_sub_cancel_left i k
    simp_rw [hadd]
    have hrange :
        ∑ k ∈ Finset.range (L + twoS + 1 - i), Nat.choose L k =
          ∑ k ∈ Finset.range (L + 1), Nat.choose L k := by
      symm
      have hsub : Finset.range (L + 1) ⊆ Finset.range (L + twoS + 1 - i) := by
        have hle : L + 1 ≤ L + twoS + 1 - i := by omega
        exact Finset.range_mono hle
      refine Finset.sum_subset hsub ?_
      intro k hk1 hk2
      simp only [Finset.mem_range, not_lt] at hk1 hk2
      exact Nat.choose_eq_zero_of_lt (Nat.lt_of_succ_le hk2)
    rw [hrange, Nat.sum_range_choose]
  rw [Finset.sum_congr rfl hinner, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_comm]

/-- Unconditional telescoping difference for `kondoCount`. -/
theorem kondoCount_succ_sub (twoS L M : ℕ) :
    (kondoCount twoS L (M + 1) : ℤ) - (kondoCount twoS L M : ℤ) =
      (Nat.choose L (M + 1) : ℤ) -
        if twoS ≤ M then (Nat.choose L (M - twoS) : ℤ) else 0 := by
  unfold kondoCount
  push_cast
  rw [Finset.sum_range_succ' _ twoS, Finset.sum_range_succ _ twoS]
  have hcancel :
      ∑ k ∈ Finset.range twoS,
        (if k + 1 ≤ M + 1 then (Nat.choose L (M + 1 - (k + 1)) : ℤ) else 0) =
        ∑ k ∈ Finset.range twoS,
          (if k ≤ M then (Nat.choose L (M - k) : ℤ) else 0) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    have hiff : k + 1 ≤ M + 1 ↔ k ≤ M := by omega
    by_cases hk : k + 1 ≤ M + 1
    · have hk' : k ≤ M := hiff.mp hk
      simp [hk, hk', Nat.succ_sub_succ]
    · have hk' : ¬ (k ≤ M) := mt hiff.mpr hk
      simp [hk, hk']
  rw [hcancel]
  simp only [Nat.zero_le, ↓reduceIte, Nat.sub_zero]
  ring

/-- Eq. (17) of Shu et al.: untwisted Kondo count `c_s^K(L; M) - c_s^K(L; M - 1)` for `1 ≤ M`. -/
theorem kondoCount_sub_pred (twoS L M : ℕ) (hM : 1 ≤ M) :
    (kondoCount twoS L M : ℤ) - (kondoCount twoS L (M - 1) : ℤ) =
      (Nat.choose L M : ℤ) -
        if twoS + 1 ≤ M then (Nat.choose L (M - twoS - 1) : ℤ) else 0 := by
  have hM' : M - 1 + 1 = M := Nat.sub_add_cancel hM
  have h := kondoCount_succ_sub twoS L (M - 1)
  rw [hM'] at h
  rw [h]
  have hiff : twoS ≤ M - 1 ↔ twoS + 1 ≤ M := by omega
  by_cases hle : twoS ≤ M - 1
  · have hsub : M - 1 - twoS = M - twoS - 1 := by omega
    simp [hle, hiff.mp hle, hsub]
  · simp [hle, mt hiff.mpr hle]

/-! ## Part 2B: Spin-s t-J Model & Foerster–Karowski Identity (Eqs. 18–21) -/

/-- Eq. (19) of Shu et al.: twisted spin-`s` `t`-`J` count `c_s^{tJ}(L; M1, M2)`. -/
def tJCount (twoS L M1 M2 : ℕ) : ℕ :=
  Nat.choose L M1 * Fintype.card (restrictedOccupancy2D twoS M1 M2)

/-- Specialization of `tJCount` at `s = 1/2` (`twoS = 1`). -/
theorem tJCount_one_eq (L M1 M2 : ℕ) :
    tJCount 1 L M1 M2 = Nat.choose L M1 * Nat.choose M1 M2 := by
  rw [tJCount, card_restrictedOccupancy2D_one]

/-- Total spin-`s` `t`-`J` state count is `(2s + 2)^L`. -/
theorem sum_tJCount (twoS L : ℕ) :
    ∑ M1 ∈ Finset.range (L + 1),
      ∑ M2 ∈ Finset.range (twoS * M1 + 1), tJCount twoS L M1 M2 = (twoS + 2) ^ L := by
  simp_rw [tJCount, ← Finset.mul_sum, sum_card_restrictedOccupancy2D]
  have hadd : twoS + 2 = (twoS + 1) + 1 := by omega
  rw [hadd, add_pow]
  refine Finset.sum_congr rfl fun M1 _ => ?_
  simp [mul_comm]

/-- Eq. (20) of Shu et al.: untwisted `t`-`J` alternating sum (guarded by `i + 1 ≤ M1`). -/
def tJUntwistedCount (twoS L M1 M2 : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (M2 + 1),
    (-1 : ℤ) ^ i *
      ((tJCount twoS L M1 (M2 - i) : ℤ) -
        if i + 1 ≤ M1 then (tJCount twoS L (M1 - i - 1) (M2 - i) : ℤ) else 0)

/-- Vacuum case `(M1, M2) = (0, 0)` of Eq. (20) at `s = 1/2`: equals `1`. -/
theorem tJUntwistedCount_one_zero_zero (L : ℕ) :
    tJUntwistedCount 1 L 0 0 = 1 := by
  simp [tJUntwistedCount, tJCount_one_eq]

/-- Boundary case `M2 = M1 ≥ 1` of Eq. (20) at `s = 1/2`: equals `0`. -/
theorem tJUntwistedCount_one_self (L M1 : ℕ) (hM1 : 1 ≤ M1) :
    tJUntwistedCount 1 L M1 M1 = 0 := by
  unfold tJUntwistedCount
  simp_rw [tJCount_one_eq]
  have hzero : ∀ i ∈ Finset.range (M1 + 1),
      (-1 : ℤ) ^ i *
        (((Nat.choose L M1 * Nat.choose M1 (M1 - i) : ℕ) : ℤ) -
          if i + 1 ≤ M1 then
            ((Nat.choose L (M1 - i - 1) * Nat.choose (M1 - i - 1) (M1 - i) : ℕ) : ℤ)
          else 0) =
        (Nat.choose L M1 : ℤ) * ((-1 : ℤ) ^ i * (Nat.choose M1 i : ℤ)) := by
    intro i hi
    have hi_le : i ≤ M1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have h2 : (if i + 1 ≤ M1 then
        ((Nat.choose L (M1 - i - 1) * Nat.choose (M1 - i - 1) (M1 - i) : ℕ) : ℤ) else 0) = 0 := by
      split_ifs with hlt
      · have hlt' : M1 - i - 1 < M1 - i := by omega
        simp [Nat.choose_eq_zero_of_lt hlt']
      · rfl
    rw [h2, sub_zero, Nat.choose_symm hi_le]
    push_cast
    ring
  rw [Finset.sum_congr rfl hzero, ← Finset.mul_sum]
  rw [Int.alternating_sum_range_choose_of_ne (Nat.pos_iff_ne_zero.mp hM1), mul_zero]

private lemma neg_one_pow_sub_mul_neg_one_pow (M k : ℕ) (hk : k ≤ M) :
    (-1 : ℤ) ^ (M - k) = (-1 : ℤ) ^ M * (-1 : ℤ) ^ k := by
  have h1 : (-1 : ℤ) ^ (M - k) * (-1 : ℤ) ^ k = (-1 : ℤ) ^ M := by
    rw [← pow_add, Nat.sub_add_cancel hk]
  have hsq : (-1 : ℤ) ^ (2 * k) = 1 := by rw [pow_mul]; simp
  calc
    (-1 : ℤ) ^ (M - k) = (-1 : ℤ) ^ (M - k) * ((-1 : ℤ) ^ k * (-1 : ℤ) ^ k) := by
      rw [← pow_add, ← two_mul, hsq, mul_one]
    _ = ((-1 : ℤ) ^ (M - k) * (-1 : ℤ) ^ k) * (-1 : ℤ) ^ k := by ring
    _ = (-1 : ℤ) ^ M * (-1 : ℤ) ^ k := by rw [h1]

private lemma alt_sum_choose_rev (N M : ℕ) (hN : 1 ≤ N) :
    (∑ i ∈ Finset.range (M + 1), (-1 : ℤ) ^ i * (Nat.choose N (M - i) : ℤ)) =
      (Nat.choose (N - 1) M : ℤ) := by
  have hrev := Finset.sum_range_reflect
    (fun k => (-1 : ℤ) ^ (M - k) * (Nat.choose N k : ℤ)) (M + 1)
  have hsimp :
      (∑ i ∈ Finset.range (M + 1),
        (-1 : ℤ) ^ (M - (M + 1 - 1 - i)) * (Nat.choose N (M + 1 - 1 - i) : ℤ)) =
        ∑ i ∈ Finset.range (M + 1), (-1 : ℤ) ^ i * (Nat.choose N (M - i) : ℤ) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi_le : i ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have h1 : M + 1 - 1 - i = M - i := by omega
    have h2 : M - (M - i) = i := Nat.sub_sub_self hi_le
    rw [h1, h2]
  rw [← hsimp, hrev]
  have hmul :
      ∑ k ∈ Finset.range (M + 1), (-1 : ℤ) ^ (M - k) * (Nat.choose N k : ℤ) =
        (-1 : ℤ) ^ M *
          ∑ k ∈ Finset.range (M + 1), (-1 : ℤ) ^ k * (Nat.choose ((N - 1) + 1) k : ℤ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk_le : k ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [neg_one_pow_sub_mul_neg_one_pow M k hk_le, Nat.sub_add_cancel hN]
    ring
  rw [hmul, Int.alternating_sum_range_choose_eq_choose]
  have hsq : (-1 : ℤ) ^ (2 * M) = 1 := by rw [pow_mul]; simp
  calc
    (-1 : ℤ) ^ M * ((-1 : ℤ) ^ M * (Nat.choose (N - 1) M : ℤ))
        = ((-1 : ℤ) ^ M * (-1 : ℤ) ^ M) * (Nat.choose (N - 1) M : ℤ) := by ring
    _ = (Nat.choose (N - 1) M : ℤ) := by
      rw [← pow_add, ← two_mul, hsq, one_mul]

/-- Closed binomial difference for `tJUntwistedCount 1 L M1 M2` when `1 ≤ M1 ≤ L` and `M2 < M1`. -/
theorem tJUntwistedCount_one_eq_choose (L M1 M2 : ℕ)
    (h1 : 1 ≤ M1) (h2 : M1 ≤ L) (h3 : M2 < M1) :
    tJUntwistedCount 1 L M1 M2 =
      (Nat.choose L M1 * Nat.choose (M1 - 1) M2 : ℤ) -
        (Nat.choose L (M1 - M2 - 1) * Nat.choose (L - M1 + M2) M2 : ℤ) := by
  unfold tJUntwistedCount
  simp_rw [tJCount_one_eq]
  have hsplit :
      (∑ i ∈ Finset.range (M2 + 1),
        (-1 : ℤ) ^ i *
          (((Nat.choose L M1 * Nat.choose M1 (M2 - i) : ℕ) : ℤ) -
            if i + 1 ≤ M1 then
              ((Nat.choose L (M1 - i - 1) * Nat.choose (M1 - i - 1) (M2 - i) : ℕ) : ℤ)
            else 0)) =
        (∑ i ∈ Finset.range (M2 + 1),
          (Nat.choose L M1 : ℤ) * ((-1 : ℤ) ^ i * (Nat.choose M1 (M2 - i) : ℤ))) -
        (∑ i ∈ Finset.range (M2 + 1),
          (Nat.choose L (M1 - M2 - 1) : ℤ) *
            ((-1 : ℤ) ^ i * (Nat.choose (L - M1 + M2 + 1) (M2 - i) : ℤ))) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi_le : i ≤ M2 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hi1 : i + 1 ≤ M1 := lt_of_le_of_lt hi_le h3
    simp only [hi1, ↓reduceIte]
    have hsym : Nat.choose (M1 - i - 1) (M2 - i) =
        Nat.choose (M1 - i - 1) (M1 - M2 - 1) := by
      apply Nat.choose_symm_of_eq_add
      omega
    have htrinom := Nat.choose_mul (n := L) (k := M1 - i - 1) (s := M1 - M2 - 1) (by omega)
    have hLM1 : L - M1 + M1 = L := Nat.sub_add_cancel h2
    have hsub1 : L - (M1 - M2 - 1) = L - M1 + M2 + 1 := by omega
    have hsub2 : M1 - i - 1 - (M1 - M2 - 1) = M2 - i := by omega
    rw [hsym, htrinom, hsub1, hsub2]
    push_cast
    ring
  rw [hsplit, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [alt_sum_choose_rev M1 M2 h1]
  have hpos : 1 ≤ L - M1 + M2 + 1 := Nat.le_add_left 1 _
  rw [alt_sum_choose_rev (L - M1 + M2 + 1) M2 hpos]
  have h2' : L - M1 + M2 + 1 - 1 = L - M1 + M2 := by omega
  rw [h2']

/-- Cleared-denominator Foerster–Karowski identity (Eq. 21) over `ℤ`. -/
theorem tJUntwistedCount_one_mul_denom (L M1 M2 : ℕ)
    (h1 : 1 ≤ M1) (h2 : M1 ≤ L) (h3 : M2 < M1) :
    (M1 : ℤ) * (Nat.factorial M2 : ℤ) * (Nat.factorial (L - M1) : ℤ) *
      (Nat.factorial (M1 - M2 - 1) : ℤ) * ((L : ℤ) - M1 + M2 + 1) *
      tJUntwistedCount 1 L M1 M2 =
      (Nat.factorial L : ℤ) * ((L : ℤ) - 2 * M1 + M2 + 1) := by
  rw [tJUntwistedCount_one_eq_choose L M1 M2 h1 h2 h3, mul_sub]
  have hc1 : (Nat.choose L M1 * Nat.factorial M1 * Nat.factorial (L - M1) : ℤ) =
      (Nat.factorial L : ℤ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial h2
  have hc2 : (Nat.choose (M1 - 1) M2 * Nat.factorial M2 * Nat.factorial (M1 - M2 - 1) : ℤ) =
      (Nat.factorial (M1 - 1) : ℤ) := by
    have hsub : M1 - 1 - M2 = M1 - M2 - 1 := by omega
    have hnat := Nat.choose_mul_factorial_mul_factorial (n := M1 - 1) (k := M2) (by omega)
    rw [hsub] at hnat
    exact_mod_cast hnat
  have hm1_fac : (M1 : ℤ) * (Nat.factorial (M1 - 1) : ℤ) = (Nat.factorial M1 : ℤ) := by
    have hM1' : M1 - 1 + 1 = M1 := Nat.sub_add_cancel h1
    have hM1Z : (M1 : ℤ) = ((M1 - 1 : ℕ) : ℤ) + 1 := by omega
    conv_rhs => rw [← hM1', Nat.factorial_succ]
    push_cast
    rw [hM1Z]
  have hterm1 :
      (M1 : ℤ) * (Nat.factorial M2 : ℤ) * (Nat.factorial (L - M1) : ℤ) *
        (Nat.factorial (M1 - M2 - 1) : ℤ) * ((L : ℤ) - M1 + M2 + 1) *
        (Nat.choose L M1 * Nat.choose (M1 - 1) M2 : ℤ) =
        (Nat.factorial L : ℤ) * ((L : ℤ) - M1 + M2 + 1) := by
    calc
      _ = (Nat.choose L M1 * ((M1 : ℤ) * (Nat.choose (M1 - 1) M2 * Nat.factorial M2 *
            Nat.factorial (M1 - M2 - 1))) * Nat.factorial (L - M1)) *
            ((L : ℤ) - M1 + M2 + 1) := by ring
      _ = (Nat.choose L M1 * Nat.factorial M1 * Nat.factorial (L - M1)) *
            ((L : ℤ) - M1 + M2 + 1) := by rw [hc2, hm1_fac]
      _ = (Nat.factorial L : ℤ) * ((L : ℤ) - M1 + M2 + 1) := by rw [hc1]
  have hc3 : (Nat.choose L (M1 - M2 - 1) * Nat.factorial (M1 - M2 - 1) *
      Nat.factorial (L - M1 + M2 + 1) : ℤ) = (Nat.factorial L : ℤ) := by
    have hsub : L - (M1 - M2 - 1) = L - M1 + M2 + 1 := by omega
    have hnat := Nat.choose_mul_factorial_mul_factorial (n := L) (k := M1 - M2 - 1) (by omega)
    rw [hsub] at hnat
    exact_mod_cast hnat
  have hc4 : (Nat.choose (L - M1 + M2) M2 * Nat.factorial M2 * Nat.factorial (L - M1) : ℤ) =
      (Nat.factorial (L - M1 + M2) : ℤ) := by
    have hsub : L - M1 + M2 - M2 = L - M1 := by omega
    have hnat := Nat.choose_mul_factorial_mul_factorial (n := L - M1 + M2) (k := M2) (by omega)
    rw [hsub] at hnat
    exact_mod_cast hnat
  have hfac_l :
      ((L : ℤ) - M1 + M2 + 1) * (Nat.factorial (L - M1 + M2) : ℤ) =
        (Nat.factorial (L - M1 + M2 + 1) : ℤ) := by
    have hcast : ((L : ℤ) - M1 + M2 + 1) = ((L - M1 + M2 + 1 : ℕ) : ℤ) := by omega
    rw [hcast]
    exact_mod_cast Nat.factorial_succ (L - M1 + M2)
  have hterm2 :
      (M1 : ℤ) * (Nat.factorial M2 : ℤ) * (Nat.factorial (L - M1) : ℤ) *
        (Nat.factorial (M1 - M2 - 1) : ℤ) * ((L : ℤ) - M1 + M2 + 1) *
        (Nat.choose L (M1 - M2 - 1) * Nat.choose (L - M1 + M2) M2 : ℤ) =
        (Nat.factorial L : ℤ) * M1 := by
    calc
      _ = (Nat.choose L (M1 - M2 - 1) * Nat.factorial (M1 - M2 - 1) *
            (((L : ℤ) - M1 + M2 + 1) * (Nat.choose (L - M1 + M2) M2 *
              Nat.factorial M2 * Nat.factorial (L - M1)))) * M1 := by ring
      _ = (Nat.choose L (M1 - M2 - 1) * Nat.factorial (M1 - M2 - 1) *
            Nat.factorial (L - M1 + M2 + 1)) * M1 := by rw [hc4, hfac_l]
      _ = (Nat.factorial L : ℤ) * M1 := by rw [hc3]
  rw [hterm1, hterm2]
  ring

/-- Eq. (21) of Shu et al. (Foerster–Karowski identity at `s = 1/2`) in `ℚ`.
Note: the final denominator factor `(L - M1 + M2 + 1)` has no factorial. -/
theorem tJUntwistedCount_one_eq_div (L M1 M2 : ℕ)
    (h1 : 1 ≤ M1) (h2 : M1 ≤ L) (h3 : M2 < M1) :
    (tJUntwistedCount 1 L M1 M2 : ℚ) =
      ((Nat.factorial L : ℚ) * ((L : ℚ) - 2 * M1 + M2 + 1)) /
        ((M1 : ℚ) * (Nat.factorial M2 : ℚ) * (Nat.factorial (L - M1) : ℚ) *
          (Nat.factorial (M1 - M2 - 1) : ℚ) * ((L : ℚ) - M1 + M2 + 1)) := by
  have hmul :
      ((M1 : ℚ) * (Nat.factorial M2 : ℚ) * (Nat.factorial (L - M1) : ℚ) *
        (Nat.factorial (M1 - M2 - 1) : ℚ) * ((L : ℚ) - M1 + M2 + 1)) *
        (tJUntwistedCount 1 L M1 M2 : ℚ) =
        (Nat.factorial L : ℚ) * ((L : ℚ) - 2 * M1 + M2 + 1) := by
    exact_mod_cast tJUntwistedCount_one_mul_denom L M1 M2 h1 h2 h3
  have hM1ne : (M1 : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp h1)
  have hLne : ((L : ℚ) - M1 + M2 + 1) ≠ 0 := by
    have hLle : (M1 : ℚ) ≤ (L : ℚ) := Nat.cast_le.mpr h2
    have hM2ge : (0 : ℚ) ≤ (M2 : ℚ) := Nat.cast_nonneg M2
    linarith
  have hden :
      (M1 : ℚ) * (Nat.factorial M2 : ℚ) * (Nat.factorial (L - M1) : ℚ) *
        (Nat.factorial (M1 - M2 - 1) : ℚ) * ((L : ℚ) - M1 + M2 + 1) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hM1ne ?_) ?_) ?_) hLne
    · exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    · exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    · exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  exact eq_div_of_mul_eq hden (by rw [mul_comm]; exact hmul)

/-! ## Part 2C: SU(3) Singular Loci, Highest-Weight Alternating Sum & Weyl Character -/

/-- `SU(3)` restricted-occupancy count `c_s(L; M1, M2)`. -/
def c3D2 (twoS L M1 M2 : ℕ) : ℕ :=
  Fintype.card (restrictedOccupancy3D twoS L 2 ![M1, M2])

/-- Vanishing of `c3D2` outside `M2 ≤ M1 ≤ 2sL`. -/
theorem c3D2_eq_zero_of_lt (twoS L M1 M2 : ℕ) (h : M1 < M2 ∨ twoS * L < M1) :
    c3D2 twoS L M1 M2 = 0 := by
  unfold c3D2
  rw [Fintype.card_eq_zero_iff]
  refine ⟨fun n => ?_⟩
  rcases h with h1 | h2
  · have hsum : ∑ α : Fin L, n.1 1 α ≤ ∑ α : Fin L, n.1 0 α :=
      Finset.sum_le_sum fun α _ => n.2.2.1 α (by decide : (0 : Fin 2) ≤ 1)
    have h0 := n.2.2.2 0
    have h1' := n.2.2.2 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at h0 h1'
    omega
  · have hsum : ∑ α : Fin L, n.1 0 α ≤ ∑ _α : Fin L, twoS :=
      Finset.sum_le_sum fun α _ => n.2.1 0 α
    have h0 := n.2.2.2 0
    simp only [Matrix.cons_val_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, mul_comm L twoS] at h0 hsum
    omega

private def restrictedOccupancy3DOneTwoEquiv (L M1 M2 : ℕ) :
    restrictedOccupancy3D 1 L 2 ![M1, M2] ≃
      { p : Finset (Fin L) × Finset (Fin L) //
        p.2 ⊆ p.1 ∧ p.1.card = M1 ∧ p.2.card = M2 } where
  toFun n :=
    let S1 : Finset (Fin L) := Finset.univ.filter (fun α => n.1 0 α = 1)
    let S2 : Finset (Fin L) := Finset.univ.filter (fun α => n.1 1 α = 1)
    have hS1 : S1.card = M1 := by
      have hsum : ∑ α : Fin L, n.1 0 α = ∑ α : Fin L, if n.1 0 α = 1 then 1 else 0 := by
        refine Finset.sum_congr rfl fun α _ => ?_
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (n.2.1 0 α) with h | h <;> simp [h]
      have h0 : ∑ α : Fin L, n.1 0 α = M1 := by simpa using n.2.2.2 0
      rw [hsum] at h0
      simpa [S1, Finset.sum_boole] using h0
    have hS2sub : S2 ⊆ S1 := by
      intro α hα
      simp only [S1, S2, Finset.mem_filter, Finset.mem_univ, true_and] at hα ⊢
      have hle1 := n.2.1 0 α
      have hle2 : n.1 1 α ≤ n.1 0 α := n.2.2.1 α (by decide : (0 : Fin 2) ≤ 1)
      omega
    have hS2 : S2.card = M2 := by
      have hsum : ∑ α : Fin L, n.1 1 α = ∑ α : Fin L, if n.1 1 α = 1 then 1 else 0 := by
        refine Finset.sum_congr rfl fun α _ => ?_
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (n.2.1 1 α) with h | h <;> simp [h]
      have h1 : ∑ α : Fin L, n.1 1 α = M2 := by simpa using n.2.2.2 1
      rw [hsum] at h1
      simpa [S2, Finset.sum_boole] using h1
    ⟨(S1, S2), hS2sub, hS1, hS2⟩
  invFun x :=
    ⟨fun a α => if a = 0 then (if α ∈ x.1.1 then 1 else 0) else (if α ∈ x.1.2 then 1 else 0),
      fun a α => by fin_cases a <;> dsimp only <;> split_ifs <;> omega,
      fun α a b hab => by
        fin_cases a <;> fin_cases b
        · exact le_rfl
        · by_cases h2 : α ∈ x.1.2
          · simp [h2, x.2.1 h2]
          · simp [h2]
        · exact absurd hab (by decide)
        · exact le_rfl,
      fun a => by
        fin_cases a
        · simp [x.2.2.1]
        · simp [x.2.2.2]⟩
  left_inv n := Subtype.ext (funext fun a => funext fun α => by
    fin_cases a
    · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (n.2.1 0 α) with h | h <;> simp [h]
    · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (n.2.1 1 α) with h | h <;> simp [h])
  right_inv x := Subtype.ext (Prod.ext (by ext α; simp) (by ext α; simp))

/-- At `s = 1/2` (`twoS = 1`), `c_{1/2}(L; M1, M2) = choose L M1 * choose M1 M2`. -/
theorem c3D2_one_eq (L M1 M2 : ℕ) :
    c3D2 1 L M1 M2 = Nat.choose L M1 * Nat.choose M1 M2 := by
  classical
  unfold c3D2
  have heq :
      { p : Finset (Fin L) × Finset (Fin L) //
        p.2 ⊆ p.1 ∧ p.1.card = M1 ∧ p.2.card = M2 } ≃
        (S1 : { S : Finset (Fin L) // S.card = M1 }) × S1.1.powersetCard M2 :=
    { toFun := fun p => ⟨⟨p.1.1, p.2.2.1⟩, ⟨p.1.2, Finset.mem_powersetCard.mpr ⟨p.2.1, p.2.2.2⟩⟩⟩
      invFun := fun x =>
        ⟨(x.1.1, x.2.1), (Finset.mem_powersetCard.mp x.2.2).1, x.1.2,
          (Finset.mem_powersetCard.mp x.2.2).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr ((restrictedOccupancy3DOneTwoEquiv L M1 M2).trans heq),
    Fintype.card_sigma]
  have hfiber : ∀ S1 : { S : Finset (Fin L) // S.card = M1 },
      Fintype.card (S1.1.powersetCard M2) = Nat.choose M1 M2 := by
    intro S1
    rw [Fintype.card_coe, Finset.card_powersetCard, S1.2]
  simp_rw [hfiber, Finset.sum_const, Finset.card_univ]
  have h1 : Fintype.card { S : Finset (Fin L) // S.card = M1 } = Nat.choose L M1 := by
    rw [← card_restrictedOccupancy2D_one L M1]
    exact Fintype.card_congr (restrictedOccupancy2DOneEquiv L M1).symm
  rw [smul_eq_mul, h1]

/-- Eq. (13) of Shu et al.: partially untwisted `SU(r + 1)` count when `t_a → 0`. -/
def suPartialUntwisted (twoS L r : ℕ) (M : Fin r → ℕ) (a : Fin r) : ℤ :=
  (Fintype.card (restrictedOccupancy3D twoS L r M) : ℤ) -
    if 1 ≤ M a then
      (Fintype.card (restrictedOccupancy3D twoS L r (Function.update M a (M a - 1))) : ℤ)
    else 0

/-- Eq. (14) of Shu et al.: `SU(3)` singular locus `t_1 + t_2 = 0`. -/
def su3DiagSingularCount (twoS L M1 M2 : ℕ) : ℤ :=
  (c3D2 twoS L M1 M2 : ℤ) -
    if 1 ≤ M1 ∧ 1 ≤ M2 then (c3D2 twoS L (M1 - 1) (M2 - 1) : ℤ) else 0

/-- Eq. (15) of Shu et al.: `SU(3)` highest-weight alternating sum (fully untwisted `t_1, t_2 = 0`). -/
def su3HighestWeightCount (twoS L M1 M2 : ℕ) : ℤ :=
  (c3D2 twoS L M1 M2 : ℤ)
  - (if 1 ≤ M1 then (c3D2 twoS L (M1 - 1) M2 : ℤ) else 0)
  - (if 1 ≤ M2 then (c3D2 twoS L M1 (M2 - 1) : ℤ) else 0)
  + (if 2 ≤ M1 ∧ 1 ≤ M2 then (c3D2 twoS L (M1 - 2) (M2 - 1) : ℤ) else 0)
  + (if 1 ≤ M1 ∧ 2 ≤ M2 then (c3D2 twoS L (M1 - 1) (M2 - 2) : ℤ) else 0)
  - (if 2 ≤ M1 ∧ 2 ≤ M2 then (c3D2 twoS L (M1 - 2) (M2 - 2) : ℤ) else 0)

private lemma c3D2_one_mul_denom_eq (L a b c : ℕ) (hsum : a + b + c = L) :
    ((Nat.factorial a * Nat.factorial b * Nat.factorial c : ℕ) : ℤ) *
      (c3D2 1 L (b + c) c : ℤ) = (Nat.factorial L : ℤ) := by
  rw [c3D2_one_eq]
  have hsum' : a + (b + c) = L := by simpa [add_assoc] using hsum
  have hbc : b + c ≤ L := le_trans (Nat.le_add_left (b + c) a) hsum'.le
  have hc : c ≤ b + c := Nat.le_add_left c b
  have h1 := Nat.choose_mul_factorial_mul_factorial hbc
  have h2 := Nat.choose_mul_factorial_mul_factorial hc
  have hsub1 : L - (b + c) = a := Nat.sub_eq_of_eq_add (by rw [← hsum', add_comm a])
  have hsub2 : b + c - c = b := Nat.add_sub_cancel b c
  rw [hsub1] at h1
  rw [hsub2] at h2
  have hnat : Nat.factorial a * Nat.factorial b * Nat.factorial c *
      (Nat.choose L (b + c) * Nat.choose (b + c) c) = Nat.factorial L := by
    calc
      Nat.factorial a * Nat.factorial b * Nat.factorial c *
          (Nat.choose L (b + c) * Nat.choose (b + c) c)
          = Nat.choose L (b + c) * (Nat.choose (b + c) c * Nat.factorial c * Nat.factorial b) *
              Nat.factorial a := by ring
      _ = Nat.choose L (b + c) * Nat.factorial (b + c) * Nat.factorial a := by rw [h2]
      _ = Nat.factorial L := h1
  exact_mod_cast hnat

/-- Cleared-denominator 3-row hook-length / SYT formula for `su3HighestWeightCount 1 L M1 M2`. -/
theorem su3HighestWeightCount_one_mul_denom (L M1 M2 : ℕ) (h1 : M2 ≤ M1) (h2 : M1 ≤ L) :
    ((Nat.factorial (L - M1 + 2) * Nat.factorial (M1 - M2 + 1) * Nat.factorial M2 : ℕ) : ℤ) *
      su3HighestWeightCount 1 L M1 M2 =
      (Nat.factorial L : ℤ) *
        (((L - M1 : ℕ) : ℤ) - ((M1 - M2 : ℕ) : ℤ) + 1) *
        (((M1 - M2 : ℕ) : ℤ) - (M2 : ℤ) + 1) *
        (((L - M1 : ℕ) : ℤ) - (M2 : ℤ) + 2) := by
  set l0 : ℕ := L - M1
  set l1 : ℕ := M1 - M2
  set l2 : ℕ := M2
  have hM1 : M1 = l1 + l2 := (Nat.sub_add_cancel h1).symm
  have hsum : l0 + l1 + l2 = L := by rw [add_assoc, ← hM1, Nat.sub_add_cancel h2]
  have hL0 : L - M1 + 2 = l0 + 2 := rfl
  have hL1 : M1 - M2 + 1 = l1 + 1 := rfl
  set D : ℤ := ((Nat.factorial (l0 + 2) * Nat.factorial (l1 + 1) * Nat.factorial l2 : ℕ) : ℤ)
  have hfac0 : (Nat.factorial (l0 + 2) : ℤ) =
      ((l0 : ℤ) + 2) * ((l0 : ℤ) + 1) * (Nat.factorial l0 : ℤ) := by
    have := Nat.factorial_succ (l0 + 1)
    have := Nat.factorial_succ l0
    push_cast [Nat.factorial_succ]
    ring
  have hfac1 : (Nat.factorial (l1 + 1) : ℤ) = ((l1 : ℤ) + 1) * (Nat.factorial l1 : ℤ) := by
    push_cast [Nat.factorial_succ]
    ring
  have ht1 : D * (c3D2 1 L M1 M2 : ℤ) =
      (Nat.factorial L : ℤ) * ((l0 : ℤ) + 2) * ((l0 : ℤ) + 1) * ((l1 : ℤ) + 1) := by
    have hc := c3D2_one_mul_denom_eq L l0 l1 l2 hsum
    rw [← hM1] at hc
    calc
      D * (c3D2 1 L M1 M2 : ℤ)
          = ((l0 : ℤ) + 2) * ((l0 : ℤ) + 1) * ((l1 : ℤ) + 1) *
              (((Nat.factorial l0 * Nat.factorial l1 * Nat.factorial l2 : ℕ) : ℤ) *
                (c3D2 1 L M1 M2 : ℤ)) := by
            simp only [D, Nat.cast_mul, hfac0, hfac1]
            ring
      _ = _ := by rw [hc]; ring
  have ht2 : D * (if 1 ≤ M1 then (c3D2 1 L (M1 - 1) M2 : ℤ) else 0) =
      (Nat.factorial L : ℤ) * ((l0 : ℤ) + 2) * ((l1 : ℤ) + 1) * (l1 : ℤ) := by
    by_cases hm1 : 1 ≤ M1
    · simp only [hm1, ↓reduceIte]
      rcases eq_or_ne l1 0 with hl1z | hl1nz
      · have hlt : M1 - 1 < M2 := by omega
        rw [c3D2_eq_zero_of_lt 1 L (M1 - 1) M2 (Or.inl hlt)]
        simp [hl1z]
      · have hl1pos : 1 ≤ l1 := Nat.one_le_iff_ne_zero.mpr hl1nz
        have hsum' : (l0 + 1) + (l1 - 1) + l2 = L := by omega
        have hc := c3D2_one_mul_denom_eq L (l0 + 1) (l1 - 1) l2 hsum'
        have hm1' : l1 - 1 + l2 = M1 - 1 := by omega
        rw [hm1'] at hc
        have hfac0' : (Nat.factorial (l0 + 2) : ℤ) =
            ((l0 : ℤ) + 2) * (Nat.factorial (l0 + 1) : ℤ) := by
          push_cast [Nat.factorial_succ]; ring
        have hfac1' : (Nat.factorial l1 : ℤ) = (l1 : ℤ) * (Nat.factorial (l1 - 1) : ℤ) := by
          have hl1eq : l1 - 1 + 1 = l1 := Nat.sub_add_cancel hl1pos
          conv_lhs => rw [← hl1eq, Nat.factorial_succ]
          push_cast [hl1eq]
          rfl
        calc
          D * (c3D2 1 L (M1 - 1) M2 : ℤ)
              = ((l0 : ℤ) + 2) * ((l1 : ℤ) + 1) * (l1 : ℤ) *
                  (((Nat.factorial (l0 + 1) * Nat.factorial (l1 - 1) *
                    Nat.factorial l2 : ℕ) : ℤ) * (c3D2 1 L (M1 - 1) M2 : ℤ)) := by
                simp only [D, Nat.cast_mul, hfac0', hfac1]
                rw [hfac1']
                ring
          _ = _ := by rw [hc]; ring
    · have hl1z : l1 = 0 := by omega
      simp [hm1, hl1z]
  have ht3 : D * (if 1 ≤ M2 then (c3D2 1 L M1 (M2 - 1) : ℤ) else 0) =
      (Nat.factorial L : ℤ) * ((l0 : ℤ) + 2) * ((l0 : ℤ) + 1) * (l2 : ℤ) := by
    by_cases hm2 : 1 ≤ M2
    · simp only [hm2, ↓reduceIte]
      have hsum' : l0 + (l1 + 1) + (l2 - 1) = L := by omega
      have hc := c3D2_one_mul_denom_eq L l0 (l1 + 1) (l2 - 1) hsum'
      have hm2' : l1 + 1 + (l2 - 1) = M1 := by omega
      rw [hm2'] at hc
      have hfac2' : (Nat.factorial l2 : ℤ) = (l2 : ℤ) * (Nat.factorial (l2 - 1) : ℤ) := by
        have hl2eq : l2 - 1 + 1 = l2 := Nat.sub_add_cancel hm2
        conv_lhs => rw [← hl2eq, Nat.factorial_succ]
        push_cast [hl2eq]
        rfl
      calc
        D * (c3D2 1 L M1 (M2 - 1) : ℤ)
            = ((l0 : ℤ) + 2) * ((l0 : ℤ) + 1) * (l2 : ℤ) *
                (((Nat.factorial l0 * Nat.factorial (l1 + 1) *
                  Nat.factorial (l2 - 1) : ℕ) : ℤ) * (c3D2 1 L M1 (l2 - 1) : ℤ)) := by
              simp only [D, Nat.cast_mul, hfac0]
              rw [hfac2']
              ring
        _ = _ := by rw [hc]; ring
    · have hl2z : l2 = 0 := by omega
      simp [hm2, hl2z]
  have ht4 : D * (if 2 ≤ M1 ∧ 1 ≤ M2 then (c3D2 1 L (M1 - 2) (M2 - 1) : ℤ) else 0) =
      (Nat.factorial L : ℤ) * ((l1 : ℤ) + 1) * (l1 : ℤ) * (l2 : ℤ) := by
    by_cases hcond : 2 ≤ M1 ∧ 1 ≤ M2
    · simp only [hcond, ↓reduceIte]
      rcases eq_or_ne l1 0 with hl1z | hl1nz
      · have hlt : M1 - 2 < M2 - 1 := by omega
        rw [c3D2_eq_zero_of_lt 1 L (M1 - 2) (M2 - 1) (Or.inl hlt)]
        simp [hl1z]
      · have hl1pos : 1 ≤ l1 := Nat.one_le_iff_ne_zero.mpr hl1nz
        have hsum' : (l0 + 2) + (l1 - 1) + (l2 - 1) = L := by omega
        have hc := c3D2_one_mul_denom_eq L (l0 + 2) (l1 - 1) (l2 - 1) hsum'
        have hm1' : l1 - 1 + (l2 - 1) = M1 - 2 := by omega
        rw [hm1'] at hc
        have hfac1' : (Nat.factorial l1 : ℤ) = (l1 : ℤ) * (Nat.factorial (l1 - 1) : ℤ) := by
          have hl1eq : l1 - 1 + 1 = l1 := Nat.sub_add_cancel hl1pos
          conv_lhs => rw [← hl1eq, Nat.factorial_succ]
          push_cast [hl1eq]
          rfl
        have hfac2' : (Nat.factorial l2 : ℤ) = (l2 : ℤ) * (Nat.factorial (l2 - 1) : ℤ) := by
          have hl2eq : l2 - 1 + 1 = l2 := Nat.sub_add_cancel hcond.2
          conv_lhs => rw [← hl2eq, Nat.factorial_succ]
          push_cast [hl2eq]
          rfl
        calc
          D * (c3D2 1 L (M1 - 2) (M2 - 1) : ℤ)
              = ((l1 : ℤ) + 1) * (l1 : ℤ) * (l2 : ℤ) *
                  (((Nat.factorial (l0 + 2) * Nat.factorial (l1 - 1) *
                    Nat.factorial (l2 - 1) : ℕ) : ℤ) *
                    (c3D2 1 L (M1 - 2) (l2 - 1) : ℤ)) := by
                simp only [D, Nat.cast_mul, hfac1]
                rw [hfac1', hfac2']
                ring
          _ = _ := by rw [hc]; ring
    · simp only [hcond]
      have hzero : l1 = 0 ∨ l2 = 0 := by omega
      rcases hzero with hlz | hlz <;> simp [hlz]
  have ht5 : D * (if 1 ≤ M1 ∧ 2 ≤ M2 then (c3D2 1 L (M1 - 1) (M2 - 2) : ℤ) else 0) =
      (Nat.factorial L : ℤ) * ((l0 : ℤ) + 2) * (l2 : ℤ) * ((l2 : ℤ) - 1) := by
    by_cases hcond : 1 ≤ M1 ∧ 2 ≤ M2
    · simp only [hcond, ↓reduceIte]
      have hsum' : (l0 + 1) + (l1 + 1) + (l2 - 2) = L := by omega
      have hc := c3D2_one_mul_denom_eq L (l0 + 1) (l1 + 1) (l2 - 2) hsum'
      have hm1' : l1 + 1 + (l2 - 2) = M1 - 1 := by omega
      rw [hm1'] at hc
      have hfac0' : (Nat.factorial (l0 + 2) : ℤ) =
          ((l0 : ℤ) + 2) * (Nat.factorial (l0 + 1) : ℤ) := by
        push_cast [Nat.factorial_succ]; ring
      have hfac2' : (Nat.factorial l2 : ℤ) =
          (l2 : ℤ) * ((l2 : ℤ) - 1) * (Nat.factorial (l2 - 2) : ℤ) := by
        have hl2eq : l2 - 2 + 2 = l2 := Nat.sub_add_cancel hcond.2
        conv_lhs => rw [← hl2eq, Nat.factorial_succ, Nat.factorial_succ]
        push_cast
        have hcast : ((l2 - 2 : ℕ) : ℤ) = (l2 : ℤ) - 2 := by omega
        rw [hcast]
        ring
      calc
        D * (c3D2 1 L (M1 - 1) (M2 - 2) : ℤ)
            = ((l0 : ℤ) + 2) * (l2 : ℤ) * ((l2 : ℤ) - 1) *
                (((Nat.factorial (l0 + 1) * Nat.factorial (l1 + 1) *
                  Nat.factorial (l2 - 2) : ℕ) : ℤ) *
                  (c3D2 1 L (M1 - 1) (l2 - 2) : ℤ)) := by
              simp only [D, Nat.cast_mul, hfac0']
              rw [hfac2']
              ring
        _ = _ := by rw [hc]; ring
    · simp only [hcond]
      have hl2lt : l2 = 0 ∨ l2 = 1 := by omega
      rcases hl2lt with hl2 | hl2 <;> simp [hl2]
  have ht6 : D * (if 2 ≤ M1 ∧ 2 ≤ M2 then (c3D2 1 L (M1 - 2) (M2 - 2) : ℤ) else 0) =
      (Nat.factorial L : ℤ) * ((l1 : ℤ) + 1) * (l2 : ℤ) * ((l2 : ℤ) - 1) := by
    by_cases hcond : 2 ≤ M1 ∧ 2 ≤ M2
    · simp only [hcond, ↓reduceIte]
      have hsum' : (l0 + 2) + l1 + (l2 - 2) = L := by omega
      have hc := c3D2_one_mul_denom_eq L (l0 + 2) l1 (l2 - 2) hsum'
      have hm1' : l1 + (l2 - 2) = M1 - 2 := by omega
      rw [hm1'] at hc
      have hfac2' : (Nat.factorial l2 : ℤ) =
          (l2 : ℤ) * ((l2 : ℤ) - 1) * (Nat.factorial (l2 - 2) : ℤ) := by
        have hl2eq : l2 - 2 + 2 = l2 := Nat.sub_add_cancel hcond.2
        conv_lhs => rw [← hl2eq, Nat.factorial_succ, Nat.factorial_succ]
        push_cast
        have hcast : ((l2 - 2 : ℕ) : ℤ) = (l2 : ℤ) - 2 := by omega
        rw [hcast]
        ring
      calc
        D * (c3D2 1 L (M1 - 2) (M2 - 2) : ℤ)
            = ((l1 : ℤ) + 1) * (l2 : ℤ) * ((l2 : ℤ) - 1) *
                (((Nat.factorial (l0 + 2) * Nat.factorial l1 *
                  Nat.factorial (l2 - 2) : ℕ) : ℤ) *
                  (c3D2 1 L (M1 - 2) (l2 - 2) : ℤ)) := by
              simp only [D, Nat.cast_mul, hfac1]
              rw [hfac2']
              ring
        _ = _ := by rw [hc]; ring
    · simp only [hcond]
      have hl2lt : l2 = 0 ∨ l2 = 1 := by omega
      rcases hl2lt with hl2 | hl2 <;> simp [hl2]
  unfold su3HighestWeightCount
  change D * _ = _
  rw [mul_sub, mul_add, mul_add, mul_sub, mul_sub, ht1, ht2, ht3, ht4, ht5, ht6]
  ring

/-- Nonnegativity of the `SU(3)` `s = 1/2` highest-weight count on dominant weights. -/
theorem su3HighestWeightCount_one_nonneg (L M1 M2 : ℕ)
    (h1 : 2 * M2 ≤ M1) (h2 : 2 * M1 ≤ L + M2) :
    0 ≤ su3HighestWeightCount 1 L M1 M2 := by
  have hm12 : M2 ≤ M1 := le_trans (Nat.le_mul_of_pos_left M2 (by decide)) h1
  have hm1L : M1 ≤ L := by linarith [h1, h2]
  have hmul := su3HighestWeightCount_one_mul_denom L M1 M2 hm12 hm1L
  have hDpos : (0 : ℤ) <
      ((Nat.factorial (L - M1 + 2) * Nat.factorial (M1 - M2 + 1) * Nat.factorial M2 : ℕ) : ℤ) := by
    exact_mod_cast Nat.mul_pos (Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _))
      (Nat.factorial_pos _)
  have hfacL : (0 : ℤ) ≤ (Nat.factorial L : ℤ) := by positivity
  have hf1 : (0 : ℤ) ≤ ((L - M1 : ℕ) : ℤ) - ((M1 - M2 : ℕ) : ℤ) + 1 := by
    zify [hm12, hm1L]; linarith [h2]
  have hf2 : (0 : ℤ) ≤ ((M1 - M2 : ℕ) : ℤ) - (M2 : ℤ) + 1 := by
    zify [hm12]; linarith [h1]
  have hf3 : (0 : ℤ) ≤ ((L - M1 : ℕ) : ℤ) - (M2 : ℤ) + 2 := by
    zify [hm1L]; linarith [h1, h2]
  have hrhs : (0 : ℤ) ≤
      (Nat.factorial L : ℤ) *
        (((L - M1 : ℕ) : ℤ) - ((M1 - M2 : ℕ) : ℤ) + 1) *
        (((M1 - M2 : ℕ) : ℤ) - (M2 : ℤ) + 1) *
        (((L - M1 : ℕ) : ℤ) - (M2 : ℤ) + 2) := by
    positivity
  rw [← hmul] at hrhs
  exact nonneg_of_mul_nonneg_right hrhs hDpos

/-! ### Table 1 Concrete Evaluations (Shu et al., p. 6)
Note on Table 1 column-header swap in Source #5:
By Eq. (13), `t1 = 0` (`a = 0`) corresponds to `c_s(L; M1, M2) - c_s(L; M1 - 1, M2)` (`35, 252, 480`)
and `t2 = 0` (`a = 1`) corresponds to `c_s(L; M1, M2) - c_s(L; M1, M2 - 1)` (`105, 140, 630`).
In Table 1 of Shu et al., the headers `t1 = 0` and `t2 = 0` are swapped relative to Eq. (13), while
`generic t` (`140, 420, 840`), `t1 + t2 = 0` (`105, 252, 720`), and `t1, t2 = 0` (`21, 56, 315`)
match Eqs. (9), (14), and (15) verbatim.
-/

theorem table1_row1_generic : c3D2 1 7 4 1 = 140 := by
  rw [c3D2_one_eq]; norm_num [Nat.choose]

theorem table1_row1_t1_zero : suPartialUntwisted 1 7 2 ![4, 1] 0 = 35 := by
  rw [suPartialUntwisted, if_pos (by decide)]
  have hupd : Function.update ![4, 1] (0 : Fin 2) (![4, 1] 0 - 1) = ![3, 1] :=
    funext fun i => by fin_cases i <;> rfl
  rw [hupd]
  change (c3D2 1 7 4 1 : ℤ) - (c3D2 1 7 3 1 : ℤ) = 35
  simp only [c3D2_one_eq]; norm_num [Nat.choose]

theorem table1_row1_t2_zero : suPartialUntwisted 1 7 2 ![4, 1] 1 = 105 := by
  rw [suPartialUntwisted, if_pos (by decide)]
  have hupd : Function.update ![4, 1] (1 : Fin 2) (![4, 1] 1 - 1) = ![4, 0] :=
    funext fun i => by fin_cases i <;> rfl
  rw [hupd]
  change (c3D2 1 7 4 1 : ℤ) - (c3D2 1 7 4 0 : ℤ) = 105
  simp only [c3D2_one_eq]; norm_num [Nat.choose]

theorem table1_row1_diag : su3DiagSingularCount 1 7 4 1 = 105 := by
  simp only [su3DiagSingularCount, Nat.reduceLeDiff, and_self, ↓reduceIte, Nat.add_one_sub_one,
    c3D2_one_eq]
  norm_num [Nat.choose]

theorem table1_row1_hw : su3HighestWeightCount 1 7 4 1 = 21 := by
  simp only [su3HighestWeightCount, Nat.reduceLeDiff, ↓reduceIte, Nat.add_one_sub_one,
    and_self, Nat.reduceSub, c3D2_one_eq]
  norm_num [Nat.choose]

theorem table1_row2_generic : c3D2 1 8 4 2 = 420 := by
  rw [c3D2_one_eq]; norm_num [Nat.choose]

theorem table1_row2_t1_zero : suPartialUntwisted 1 8 2 ![4, 2] 0 = 252 := by
  rw [suPartialUntwisted, if_pos (by decide)]
  have hupd : Function.update ![4, 2] (0 : Fin 2) (![4, 2] 0 - 1) = ![3, 2] :=
    funext fun i => by fin_cases i <;> rfl
  rw [hupd]
  change (c3D2 1 8 4 2 : ℤ) - (c3D2 1 8 3 2 : ℤ) = 252
  simp only [c3D2_one_eq]; norm_num [Nat.choose]

theorem table1_row2_t2_zero : suPartialUntwisted 1 8 2 ![4, 2] 1 = 140 := by
  rw [suPartialUntwisted, if_pos (by decide)]
  have hupd : Function.update ![4, 2] (1 : Fin 2) (![4, 2] 1 - 1) = ![4, 1] :=
    funext fun i => by fin_cases i <;> rfl
  rw [hupd]
  change (c3D2 1 8 4 2 : ℤ) - (c3D2 1 8 4 1 : ℤ) = 140
  simp only [c3D2_one_eq]; norm_num [Nat.choose]

theorem table1_row2_diag : su3DiagSingularCount 1 8 4 2 = 252 := by
  simp only [su3DiagSingularCount, Nat.reduceLeDiff, and_self, ↓reduceIte, Nat.reduceSub,
    c3D2_one_eq]
  norm_num [Nat.choose]

theorem table1_row2_hw : su3HighestWeightCount 1 8 4 2 = 56 := by
  simp only [su3HighestWeightCount, Nat.reduceLeDiff, ↓reduceIte, Nat.reduceSub, and_self,
    Nat.add_one_sub_one, Nat.sub_self, c3D2_one_eq]
  norm_num [Nat.choose]

theorem table1_row3_generic : c3D2 1 10 4 1 = 840 := by
  rw [c3D2_one_eq]; norm_num [Nat.choose]

theorem table1_row3_t1_zero : suPartialUntwisted 1 10 2 ![4, 1] 0 = 480 := by
  rw [suPartialUntwisted, if_pos (by decide)]
  have hupd : Function.update ![4, 1] (0 : Fin 2) (![4, 1] 0 - 1) = ![3, 1] :=
    funext fun i => by fin_cases i <;> rfl
  rw [hupd]
  change (c3D2 1 10 4 1 : ℤ) - (c3D2 1 10 3 1 : ℤ) = 480
  simp only [c3D2_one_eq]; norm_num [Nat.choose]

theorem table1_row3_t2_zero : suPartialUntwisted 1 10 2 ![4, 1] 1 = 630 := by
  rw [suPartialUntwisted, if_pos (by decide)]
  have hupd : Function.update ![4, 1] (1 : Fin 2) (![4, 1] 1 - 1) = ![4, 0] :=
    funext fun i => by fin_cases i <;> rfl
  rw [hupd]
  change (c3D2 1 10 4 1 : ℤ) - (c3D2 1 10 4 0 : ℤ) = 630
  simp only [c3D2_one_eq]; norm_num [Nat.choose]

theorem table1_row3_diag : su3DiagSingularCount 1 10 4 1 = 720 := by
  simp only [su3DiagSingularCount, Nat.reduceLeDiff, and_self, ↓reduceIte, Nat.add_one_sub_one,
    c3D2_one_eq]
  norm_num [Nat.choose]

theorem table1_row3_hw : su3HighestWeightCount 1 10 4 1 = 315 := by
  simp only [su3HighestWeightCount, Nat.reduceLeDiff, ↓reduceIte, Nat.add_one_sub_one,
    and_self, Nat.reduceSub, c3D2_one_eq]
  norm_num [Nat.choose]

/-! ### General `twoS` Weyl Character / Vandermonde Alternant Identification -/

private noncomputable def exp3 (a b c : ℕ) : Fin 3 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm ![a, b, c]

@[simp]
private lemma exp3_apply_zero (a b c : ℕ) : exp3 a b c 0 = a := rfl

@[simp]
private lemma exp3_apply_one (a b c : ℕ) : exp3 a b c 1 = b := rfl

@[simp]
private lemma exp3_apply_two (a b c : ℕ) : exp3 a b c 2 = c := rfl

private lemma exp3_ext {m : Fin 3 →₀ ℕ} {a b c : ℕ}
    (h0 : m 0 = a) (h1 : m 1 = b) (h2 : m 2 = c) : m = exp3 a b c := by
  ext i
  fin_cases i <;> simp [h0, h1, h2]

private lemma exp3_le_iff {a b c : ℕ} {m : Fin 3 →₀ ℕ} :
    exp3 a b c ≤ m ↔ a ≤ m 0 ∧ b ≤ m 1 ∧ c ≤ m 2 := by
  rw [Finsupp.le_def]
  constructor
  · intro h
    exact ⟨h 0, h 1, h 2⟩
  · rintro ⟨h0, h1, h2⟩ i
    fin_cases i <;> assumption

/-- `SU(3)` Vandermonde determinant `(x0 - x1)(x1 - x2)(x0 - x2)` in `MvPolynomial (Fin 3) ℤ`. -/
noncomputable def su3Vandermonde : MvPolynomial (Fin 3) ℤ :=
  (MvPolynomial.X 0 - MvPolynomial.X 1) *
    (MvPolynomial.X 1 - MvPolynomial.X 2) *
    (MvPolynomial.X 0 - MvPolynomial.X 2)

/-- `su3Vandermonde` is `S_3`-alternating. -/
theorem su3Vandermonde_alternating (σ : Equiv.Perm (Fin 3)) :
    MvPolynomial.rename σ su3Vandermonde = (Equiv.Perm.sign σ : ℤ) • su3Vandermonde := by
  induction σ using Equiv.Perm.swap_induction_on with
  | one => simp
  | swap_mul f x y hxy ih =>
    have hswap_eq : ∀ a b : Fin 3, a ≠ b →
        MvPolynomial.rename (Equiv.swap a b) su3Vandermonde = -su3Vandermonde := by
      intro a b hab
      fin_cases a <;> fin_cases b
      all_goals
        first
        | exact absurd rfl hab
        | (simp only [su3Vandermonde, map_mul, map_sub, MvPolynomial.rename_X];
           simp [Equiv.swap_apply_def]; ring)
    have hren : MvPolynomial.rename (Equiv.swap x y * f) su3Vandermonde =
        MvPolynomial.rename (Equiv.swap x y) (MvPolynomial.rename f su3Vandermonde) := by
      rw [show (⇑(Equiv.swap x y * f) : Fin 3 → Fin 3) = (⇑(Equiv.swap x y)) ∘ f from rfl,
        MvPolynomial.rename_rename]
    rw [hren, ih, map_zsmul, hswap_eq x y hxy, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hxy]
    simp [smul_neg, neg_smul]

private lemma hsymm_fin3_eq_sum_siteProfile (twoS : ℕ) :
    MvPolynomial.hsymm (Fin 3) ℤ twoS =
      ∑ p : SiteProfile twoS 2,
        MvPolynomial.monomial (exp3 (twoS - p.1 0) (p.1 0 - p.1 1) (p.1 1)) (1 : ℤ) := by
  unfold MvPolynomial.hsymm
  let e : SiteProfile twoS 2 ≃ Sym (Fin 3) twoS := siteProfileEquivSym twoS 2
  rw [← Fintype.sum_equiv e.symm _ (fun p =>
      MvPolynomial.monomial (exp3 (twoS - p.1 0) (p.1 0 - p.1 1) (p.1 1)) (1 : ℤ))]
  intro s
  have hprod : (s.1.map (MvPolynomial.X : Fin 3 → MvPolynomial (Fin 3) ℤ)).prod =
      MvPolynomial.monomial
        (Finsupp.equivFunOnFinite.symm (fun i : Fin 3 => s.1.count i)) (1 : ℤ) := by
    have hs := Sym.coe_equivNatSumOfFintype_symm_apply (α := Fin 3) (n := twoS)
      ((Sym.equivNatSumOfFintype (Fin 3) twoS) s)
    have hsymm : ((Sym.equivNatSumOfFintype (Fin 3) twoS).symm
        (Sym.equivNatSumOfFintype (Fin 3) twoS s) : Multiset (Fin 3)) = s.1 :=
      congrArg Subtype.val ((Sym.equivNatSumOfFintype (Fin 3) twoS).symm_apply_apply s)
    rw [hsymm] at hs
    conv_lhs => rw [hs]
    let mapHom : Multiset (Fin 3) →+ Multiset (MvPolynomial (Fin 3) ℤ) :=
      { toFun := Multiset.map MvPolynomial.X
        map_zero' := Multiset.map_zero _
        map_add' := Multiset.map_add _ }
    change (mapHom (∑ a, ((Sym.equivNatSumOfFintype (Fin 3) twoS s).1 a) • ({a} : Multiset (Fin 3)))).prod = _
    rw [map_sum, Multiset.prod_sum]
    simp only [mapHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Multiset.map_nsmul,
      Multiset.map_singleton, Multiset.prod_nsmul, Multiset.prod_singleton]
    rw [MvPolynomial.monomial_eq, map_one, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    congr 1
  rw [hprod]
  let p := e.symm s
  have hp : e p = s := e.apply_symm_apply s
  have hcount : ∀ i : Fin 3, s.1.count i =
      padRow twoS p.1 i.val - padRow twoS p.1 (i.val + 1) := by
    intro i
    have hcoe : ((siteProfileEquivNatSum twoS 2 p).1 i) =
        padRow twoS p.1 i.val - padRow twoS p.1 (i.val + 1) := rfl
    have hev : (Sym.equivNatSumOfFintype (Fin 3) twoS s).1 i = s.1.count i := rfl
    have hps : Sym.equivNatSumOfFintype (Fin 3) twoS s = siteProfileEquivNatSum twoS 2 p := by
      rw [← hp]
      exact (Sym.equivNatSumOfFintype (Fin 3) twoS).apply_symm_apply _
    rw [← hev, hps, hcoe]
  refine congrArg (fun m => MvPolynomial.monomial m (1 : ℤ)) (exp3_ext ?_ ?_ ?_)
  · simpa [padRow] using hcount 0
  · simpa [padRow] using hcount 1
  · simpa [padRow] using hcount 2

private lemma prod_monomial_one (s : Finset (Fin L)) (g : Fin L → Fin 3 →₀ ℕ) :
    (∏ α ∈ s, MvPolynomial.monomial (g α) (1 : ℤ)) =
      MvPolynomial.monomial (∑ α ∈ s, g α) (1 : ℤ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, MvPolynomial.monomial_mul_monomial,
      mul_one]

/-- Coefficient of `(hsymm (Fin 3) ℤ twoS) ^ L` at `(2sL - M1, M1 - M2, M2)` equals `c_s(L; M1, M2)`. -/
theorem hsymm_fin3_pow_coeff_eq_c3D2 (twoS L M1 M2 : ℕ) (h1 : M2 ≤ M1) (h2 : M1 ≤ twoS * L) :
    ((MvPolynomial.hsymm (Fin 3) ℤ twoS) ^ L).coeff
        (Finsupp.equivFunOnFinite.symm ![twoS * L - M1, M1 - M2, M2]) =
      (c3D2 twoS L M1 M2 : ℤ) := by
  change ((MvPolynomial.hsymm (Fin 3) ℤ twoS) ^ L).coeff (exp3 (twoS * L - M1) (M1 - M2) M2) =
    (c3D2 twoS L M1 M2 : ℤ)
  rw [hsymm_fin3_eq_sum_siteProfile, Fintype.sum_pow, MvPolynomial.coeff_sum]
  have hprod : ∀ f : Fin L → SiteProfile twoS 2,
      (∏ α : Fin L,
        (MvPolynomial.monomial (exp3 (twoS - (f α).1 0) ((f α).1 0 - (f α).1 1) ((f α).1 1))
          (1 : ℤ))) =
        MvPolynomial.monomial
          (exp3 (∑ α : Fin L, (twoS - (f α).1 0))
            (∑ α : Fin L, ((f α).1 0 - (f α).1 1))
            (∑ α : Fin L, (f α).1 1)) (1 : ℤ) := by
    intro f
    rw [prod_monomial_one]
    refine congrArg (fun m => MvPolynomial.monomial m (1 : ℤ)) ?_
    apply Finsupp.ext
    intro i
    rw [Finsupp.finset_sum_apply]
    fin_cases i <;> simp
  simp_rw [hprod, MvPolynomial.coeff_monomial]
  have hiff : ∀ f : Fin L → SiteProfile twoS 2,
      (exp3 (∑ α : Fin L, (twoS - (f α).1 0))
        (∑ α : Fin L, ((f α).1 0 - (f α).1 1))
        (∑ α : Fin L, (f α).1 1) = exp3 (twoS * L - M1) (M1 - M2) M2) ↔
      ((∑ α : Fin L, (f α).1 0 = M1) ∧ (∑ α : Fin L, (f α).1 1 = M2)) := by
    intro f
    have h0 : ∑ α : Fin L, (twoS - (f α).1 0) + ∑ α : Fin L, (f α).1 0 = twoS * L := by
      rw [← Finset.sum_add_distrib]
      have hconst : ∑ _α : Fin L, twoS = twoS * L := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
          mul_comm L twoS]
      rw [← hconst]
      exact Finset.sum_congr rfl fun α _ => Nat.sub_add_cancel ((f α).2.1 0)
    have h1' : ∑ α : Fin L, ((f α).1 0 - (f α).1 1) + ∑ α : Fin L, (f α).1 1 =
        ∑ α : Fin L, (f α).1 0 := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun α _ =>
        Nat.sub_add_cancel ((f α).2.2 (by decide : (0 : Fin 2) ≤ 1))
    constructor
    · intro h
      have h0eq := congrArg (fun m : Fin 3 →₀ ℕ => m 0) h
      have h1eq := congrArg (fun m : Fin 3 →₀ ℕ => m 1) h
      have h2eq := congrArg (fun m : Fin 3 →₀ ℕ => m 2) h
      simp only [exp3_apply_zero, exp3_apply_one, exp3_apply_two] at h0eq h1eq h2eq
      have hM1_eq : twoS * L - (twoS * L - M1) = M1 := Nat.sub_sub_self h2
      have hM2_eq : M1 - M2 + M2 = M1 := Nat.sub_add_cancel h1
      omega
    · rintro ⟨ha, hb⟩
      apply exp3_ext
      · simp only [exp3_apply_zero]; omega
      · simp only [exp3_apply_one]; omega
      · simp only [exp3_apply_two]; exact hb
  have hsum_ite :
      ∑ f : Fin L → SiteProfile twoS 2,
        (if exp3 (∑ α : Fin L, (twoS - (f α).1 0))
            (∑ α : Fin L, ((f α).1 0 - (f α).1 1))
            (∑ α : Fin L, (f α).1 1) = exp3 (twoS * L - M1) (M1 - M2) M2 then (1 : ℤ) else 0) =
        ((Finset.univ.filter (fun f : Fin L → SiteProfile twoS 2 =>
          (∑ α : Fin L, (f α).1 0 = M1) ∧ (∑ α : Fin L, (f α).1 1 = M2))).card : ℤ) := by
    rw [Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl fun f _ => ?_
    simp [hiff f]
  rw [hsum_ite]
  congr 1
  have heq : restrictedOccupancy3D twoS L 2 ![M1, M2] ≃
      { f : Fin L → SiteProfile twoS 2 //
        (∑ α : Fin L, (f α).1 0 = M1) ∧ (∑ α : Fin L, (f α).1 1 = M2) } :=
    { toFun := fun n =>
        ⟨fun α => ⟨fun a => n.1 a α, fun a => n.2.1 a α, fun _ _ h => n.2.2.1 α h⟩,
          ⟨by simpa using n.2.2.2 0, by simpa using n.2.2.2 1⟩⟩
      invFun := fun f =>
        ⟨fun a α => (f.1 α).1 a,
          fun a α => (f.1 α).2.1 a,
          fun α a b hab => (f.1 α).2.2 hab,
          fun a => by fin_cases a <;> simp [f.2.1, f.2.2]⟩
      left_inv := fun _ => Subtype.ext (funext fun _ => funext fun _ => rfl)
      right_inv := fun _ => Subtype.ext (funext fun _ => Subtype.ext (funext fun _ => rfl)) }
  unfold c3D2
  rw [Fintype.card_congr heq, Fintype.card_subtype]

private lemma su3Vandermonde_eq_monomials :
    su3Vandermonde =
      MvPolynomial.monomial (exp3 2 1 0) (1 : ℤ)
      - MvPolynomial.monomial (exp3 1 2 0) (1 : ℤ)
      - MvPolynomial.monomial (exp3 2 0 1) (1 : ℤ)
      + MvPolynomial.monomial (exp3 0 2 1) (1 : ℤ)
      + MvPolynomial.monomial (exp3 1 0 2) (1 : ℤ)
      - MvPolynomial.monomial (exp3 0 1 2) (1 : ℤ) := by
  unfold su3Vandermonde
  have hx0 : (MvPolynomial.X 0 : MvPolynomial (Fin 3) ℤ) =
      MvPolynomial.monomial (exp3 1 0 0) 1 := by
    rw [MvPolynomial.X]
    exact congrArg (fun m => MvPolynomial.monomial m (1 : ℤ)) (exp3_ext (by simp) (by simp) (by simp))
  have hx1 : (MvPolynomial.X 1 : MvPolynomial (Fin 3) ℤ) =
      MvPolynomial.monomial (exp3 0 1 0) 1 := by
    rw [MvPolynomial.X]
    exact congrArg (fun m => MvPolynomial.monomial m (1 : ℤ)) (exp3_ext (by simp) (by simp) (by simp))
  have hx2 : (MvPolynomial.X 2 : MvPolynomial (Fin 3) ℤ) =
      MvPolynomial.monomial (exp3 0 0 1) 1 := by
    rw [MvPolynomial.X]
    exact congrArg (fun m => MvPolynomial.monomial m (1 : ℤ)) (exp3_ext (by simp) (by simp) (by simp))
  rw [hx0, hx1, hx2]
  simp only [sub_mul, mul_sub, MvPolynomial.monomial_mul_monomial]
  have ha : ∀ a1 b1 c1 a2 b2 c2 : ℕ,
      exp3 a1 b1 c1 + exp3 a2 b2 c2 = exp3 (a1 + a2) (b1 + b2) (c1 + c2) := by
    intro a1 b1 c1 a2 b2 c2
    exact exp3_ext rfl rfl rfl
  simp only [ha, mul_one]
  ring

/-- `su3HighestWeightCount twoS L M1 M2` equals the Weyl-character coefficient of
`su3Vandermonde * (hsymm (Fin 3) ℤ twoS) ^ L` at `λ + ρ = (2sL - M1 + 2, M1 - M2 + 1, M2)`. -/
theorem su3HighestWeightCount_eq_coeff_vandermonde_mul_hsymm_pow (twoS L M1 M2 : ℕ)
    (h1 : M2 ≤ M1) (h2 : M1 ≤ twoS * L) :
    su3HighestWeightCount twoS L M1 M2 =
      (su3Vandermonde * (MvPolynomial.hsymm (Fin 3) ℤ twoS) ^ L).coeff
        (Finsupp.equivFunOnFinite.symm ![twoS * L - M1 + 2, M1 - M2 + 1, M2]) := by
  set P := (MvPolynomial.hsymm (Fin 3) ℤ twoS) ^ L
  set m := exp3 (twoS * L - M1 + 2) (M1 - M2 + 1) M2
  change su3HighestWeightCount twoS L M1 M2 = (su3Vandermonde * P).coeff m
  rw [su3Vandermonde_eq_monomials, sub_mul, add_mul, add_mul, sub_mul, sub_mul]
  simp only [MvPolynomial.coeff_sub, AddMonoidAlgebra.coeff_add, Finsupp.coe_add,
    Pi.add_apply, MvPolynomial.coeff_monomial_mul', one_mul]
  have hm0 : m 0 = twoS * L - M1 + 2 := rfl
  have hm1 : m 1 = M1 - M2 + 1 := rfl
  have hm2 : m 2 = M2 := rfl
  have hc1 : (if exp3 2 1 0 ≤ m then P.coeff (m - exp3 2 1 0) else 0) =
      (c3D2 twoS L M1 M2 : ℤ) := by
    have hle : exp3 2 1 0 ≤ m := exp3_le_iff.mpr ⟨by omega, by omega, by omega⟩
    have hsub : m - exp3 2 1 0 = exp3 (twoS * L - M1) (M1 - M2) M2 :=
      exp3_ext (by simp [m]) (by simp [m]) (by simp [m])
    simp only [hle, ↓reduceIte, hsub]
    exact hsymm_fin3_pow_coeff_eq_c3D2 twoS L M1 M2 h1 h2
  have hc2 : (if exp3 1 2 0 ≤ m then P.coeff (m - exp3 1 2 0) else 0) =
      (if 1 ≤ M1 then (c3D2 twoS L (M1 - 1) M2 : ℤ) else 0) := by
    by_cases hM12 : 1 ≤ M1 - M2
    · have hM1 : 1 ≤ M1 := by omega
      have hle : exp3 1 2 0 ≤ m := exp3_le_iff.mpr ⟨by omega, by omega, by omega⟩
      have hsub : m - exp3 1 2 0 = exp3 (twoS * L - (M1 - 1)) ((M1 - 1) - M2) M2 :=
        exp3_ext (by simp [m]; omega) (by simp [m]; omega) (by simp [m])
      simp only [hle, hM1, ↓reduceIte, hsub]
      exact hsymm_fin3_pow_coeff_eq_c3D2 twoS L (M1 - 1) M2 (by omega) (by omega)
    · have hnle : ¬ (exp3 1 2 0 ≤ m) := by
        rw [exp3_le_iff]
        omega
      simp only [hnle, ↓reduceIte]
      split_ifs with hM1
      · have hlt : M1 - 1 < M2 := by omega
        rw [c3D2_eq_zero_of_lt twoS L (M1 - 1) M2 (Or.inl hlt)]
        rfl
      · rfl
  have hc3 : (if exp3 2 0 1 ≤ m then P.coeff (m - exp3 2 0 1) else 0) =
      (if 1 ≤ M2 then (c3D2 twoS L M1 (M2 - 1) : ℤ) else 0) := by
    by_cases hM2 : 1 ≤ M2
    · have hle : exp3 2 0 1 ≤ m := exp3_le_iff.mpr ⟨by omega, by omega, by omega⟩
      have hsub : m - exp3 2 0 1 = exp3 (twoS * L - M1) (M1 - (M2 - 1)) (M2 - 1) :=
        exp3_ext (by simp [m]) (by simp [m]; omega) (by simp [m])
      simp only [hle, hM2, ↓reduceIte, hsub]
      exact hsymm_fin3_pow_coeff_eq_c3D2 twoS L M1 (M2 - 1) (by omega) h2
    · have hnle : ¬ (exp3 2 0 1 ≤ m) := by
        rw [exp3_le_iff]
        omega
      simp only [hnle, hM2, ↓reduceIte]
  have hc4 : (if exp3 0 2 1 ≤ m then P.coeff (m - exp3 0 2 1) else 0) =
      (if 2 ≤ M1 ∧ 1 ≤ M2 then (c3D2 twoS L (M1 - 2) (M2 - 1) : ℤ) else 0) := by
    by_cases hcond : 1 ≤ M1 - M2 ∧ 1 ≤ M2
    · have hcond' : 2 ≤ M1 ∧ 1 ≤ M2 := ⟨by omega, hcond.2⟩
      have hle : exp3 0 2 1 ≤ m := exp3_le_iff.mpr ⟨by omega, by omega, by omega⟩
      have hsub : m - exp3 0 2 1 = exp3 (twoS * L - (M1 - 2)) ((M1 - 2) - (M2 - 1)) (M2 - 1) :=
        exp3_ext (by simp [m]; omega) (by simp [m]; omega) (by simp [m])
      simp only [hle, hcond', ↓reduceIte, hsub]
      exact hsymm_fin3_pow_coeff_eq_c3D2 twoS L (M1 - 2) (M2 - 1) (by omega) (by omega)
    · have hnle : ¬ (exp3 0 2 1 ≤ m) := by
        rw [exp3_le_iff]
        omega
      simp only [hnle, ↓reduceIte]
      split_ifs with hcond'
      · have hlt : M1 - 2 < M2 - 1 := by omega
        rw [c3D2_eq_zero_of_lt twoS L (M1 - 2) (M2 - 1) (Or.inl hlt)]
        rfl
      · rfl
  have hc5 : (if exp3 1 0 2 ≤ m then P.coeff (m - exp3 1 0 2) else 0) =
      (if 1 ≤ M1 ∧ 2 ≤ M2 then (c3D2 twoS L (M1 - 1) (M2 - 2) : ℤ) else 0) := by
    by_cases hM2 : 2 ≤ M2
    · have hcond : 1 ≤ M1 ∧ 2 ≤ M2 := ⟨by omega, hM2⟩
      have hle : exp3 1 0 2 ≤ m := exp3_le_iff.mpr ⟨by omega, by omega, by omega⟩
      have hsub : m - exp3 1 0 2 = exp3 (twoS * L - (M1 - 1)) ((M1 - 1) - (M2 - 2)) (M2 - 2) :=
        exp3_ext (by simp [m]; omega) (by simp [m]; omega) (by simp [m])
      simp only [hle, hcond, ↓reduceIte, hsub]
      exact hsymm_fin3_pow_coeff_eq_c3D2 twoS L (M1 - 1) (M2 - 2) (by omega) (by omega)
    · have hnle : ¬ (exp3 1 0 2 ≤ m) := by
        rw [exp3_le_iff]
        omega
      have hcond : ¬ (1 ≤ M1 ∧ 2 ≤ M2) := fun hc => hM2 hc.2
      simp only [hnle, hcond, ↓reduceIte]
  have hc6 : (if exp3 0 1 2 ≤ m then P.coeff (m - exp3 0 1 2) else 0) =
      (if 2 ≤ M1 ∧ 2 ≤ M2 then (c3D2 twoS L (M1 - 2) (M2 - 2) : ℤ) else 0) := by
    by_cases hM2 : 2 ≤ M2
    · have hcond : 2 ≤ M1 ∧ 2 ≤ M2 := ⟨by omega, hM2⟩
      have hle : exp3 0 1 2 ≤ m := exp3_le_iff.mpr ⟨by omega, by omega, by omega⟩
      have hsub : m - exp3 0 1 2 = exp3 (twoS * L - (M1 - 2)) ((M1 - 2) - (M2 - 2)) (M2 - 2) :=
        exp3_ext (by simp [m]; omega) (by simp [m]; omega) (by simp [m])
      simp only [hle, hcond, ↓reduceIte, hsub]
      exact hsymm_fin3_pow_coeff_eq_c3D2 twoS L (M1 - 2) (M2 - 2) (by omega) (by omega)
    · have hnle : ¬ (exp3 0 1 2 ≤ m) := by
        rw [exp3_le_iff]
        omega
      have hcond : ¬ (2 ≤ M1 ∧ 2 ≤ M2) := fun hc => hM2 hc.2
      simp only [hnle, hcond, ↓reduceIte]
  rw [hc1, hc2, hc3, hc4, hc5, hc6]
  unfold su3HighestWeightCount
  rfl

/-- The Weyl product `su3Vandermonde * (hsymm (Fin 3) ℤ twoS) ^ L` is `S_3`-alternating. -/
theorem su3Vandermonde_mul_hsymm_pow_alternating (twoS L : ℕ) (σ : Equiv.Perm (Fin 3)) :
    MvPolynomial.rename σ (su3Vandermonde * (MvPolynomial.hsymm (Fin 3) ℤ twoS) ^ L) =
      (Equiv.Perm.sign σ : ℤ) •
        (su3Vandermonde * (MvPolynomial.hsymm (Fin 3) ℤ twoS) ^ L) := by
  rw [map_mul, map_pow, su3Vandermonde_alternating, MvPolynomial.hsymm_isSymmetric (Fin 3) ℤ twoS σ,
    smul_mul_assoc]

end InfoGeometry.Integrable.RestrictedOccupancyAndBetheCounting
