/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.H3ZornE6RootSystem
import Mathlib.Algebra.Lie.BaseChange
import Mathlib.Algebra.Lie.Semisimple.Basic

/-!
# Split Chevalley Simplicity Engine and Unconditional Simplicity of `𝔣₄(4)` (`H3ZornF4Derivations`)

This module provides:

1. A generic `SplitChevalleyData (K L : Type*)` simplicity engine over any `[Field K] [CharZero K]`
   together with `SplitChevalleyData.extendScalars`, lifting any real split Chevalley presentation
   to `K ⊗[ℝ] L`.
2. Construction of the 52-dimensional Chevalley basis (`4` Cartan + `48` root operators) of
   `H3ZornF4Derivations` (`𝔣₄(4)`) by folding `H3ZornE6RootSystem`, verified via `SparseMat27` and
   `decide`, together with `f4Cartan.IsCartanSubalgebra` and `f4RootEquiv` into `CFSGPort` `F₄` roots.
3. Unconditional simplicity theorems and instances:
   - `h3ZornF4Derivations_isSimple : LieAlgebra.IsSimple ℝ H3ZornF4Derivations` (`𝔣₄(4)`)
   - `complexH3ZornF4Derivations_isSimple : LieAlgebra.IsSimple ℂ (ℂ ⊗[ℝ] H3ZornF4Derivations)` (`F₄(ℂ)`)
   - `IsSemisimple ℝ`, `HasTrivialRadical ℝ`, `center = ⊥`
   - Explicit non-commutativity witness `f4_matrix27_real_noncomm_witness`.
-/

noncomputable section

namespace InfoGeometry.Algebra

open InfoGeometry.Exceptional.CFSGPort.Chevalley
open scoped TensorProduct

section SplitChevalleyEngine

/-- Generic Vandermonde/weight-killing lemma over any field `K` of characteristic `0`, requiring
only Cartan commutativity, root eigenvectors, and nonzero distinct integer root eigenvalues. -/
theorem cartan_weight_kill_mem_generic
    {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
    {rk m : ℕ} (H : Fin rk → L) (R : Fin m → L) (ev : Fin rk → Fin m → ℤ)
    (hHH : ∀ i j : Fin rk, ⁅H i, H j⁆ = 0)
    (hHR : ∀ (i : Fin rk) (r : Fin m), ⁅H i, R r⁆ = (ev i r : K) • R r)
    (hev_nz : ∀ r : Fin m, ∃ i : Fin rk, ev i r ≠ 0)
    (hev_inj : ∀ {r₁ r₂ : Fin m}, (∀ i : Fin rk, ev i r₁ = ev i r₂) → r₁ = r₂)
    (S : Submodule K L)
    (hS : ∀ (i : Fin rk) (x : L), x ∈ S → ⁅H i, x⁆ ∈ S)
    (A : Finset (Fin m)) (h : L) (hh : h ∈ Submodule.span K (Set.range H))
    (b : Fin m → K) (hx : h + ∑ r ∈ A, b r • R r ∈ S) :
    h ∈ S ∧ ∀ r ∈ A, b r • R r ∈ S := by
  have hKillH : ∀ (u : L), u ∈ Submodule.span K (Set.range H) → ∀ i : Fin rk, ⁅H i, u⁆ = 0 := by
    intro u hu i
    induction hu using Submodule.span_induction with
    | zero => simp
    | add _ _ _ _ ih₁ ih₂ => rw [lie_add, ih₁, ih₂, add_zero]
    | smul c _ _ ih => rw [lie_smul, ih, smul_zero]
    | mem _ hm =>
      rcases hm with ⟨j, rfl⟩
      exact hHH i j
  suffices hMain : ∀ n : ℕ, ∀ (B : Finset (Fin m)) (h0 : L),
      h0 ∈ Submodule.span K (Set.range H) → B.card = n →
      ∀ (c : Fin m → K), h0 + ∑ r ∈ B, c r • R r ∈ S →
        h0 ∈ S ∧ ∀ r ∈ B, c r • R r ∈ S from
    hMain A.card A h hh rfl b hx
  intro n
  induction n with
  | zero =>
    intro B h0 hh0 hcard c hc
    rw [Finset.card_eq_zero.mp hcard] at hc ⊢
    simp only [Finset.sum_empty, add_zero] at hc
    exact ⟨hc, fun _ hr => absurd hr (Finset.notMem_empty _)⟩
  | succ n ih =>
    intro B h0 hh0 hcard c hc
    by_cases hn : n = 0
    · subst hn
      rw [Finset.card_eq_one] at hcard
      rcases hcard with ⟨r₀, rfl⟩
      simp only [Finset.sum_singleton] at hc
      obtain ⟨i₀, hi₀⟩ := hev_nz r₀
      have hbr := hS i₀ _ hc
      rw [lie_add, hKillH h0 hh0 i₀, zero_add, lie_smul, hHR, smul_smul] at hbr
      have hk₀ : (ev i₀ r₀ : K) ≠ 0 := Int.cast_ne_zero.mpr hi₀
      have hroot : c r₀ • R r₀ ∈ S := by
        have hs := S.smul_mem (ev i₀ r₀ : K)⁻¹ hbr
        rw [smul_smul, mul_comm (c r₀), ← mul_assoc, inv_mul_cancel₀ hk₀, one_mul] at hs
        exact hs
      have hh0_mem : h0 ∈ S := by
        have hsub := S.sub_mem hc hroot
        simpa [add_sub_cancel_right] using hsub
      exact ⟨hh0_mem, fun r hr => by
        rw [Finset.mem_singleton] at hr
        subst hr
        exact hroot⟩
    · have hpos : 1 < B.card := by omega
      obtain ⟨r₀, hr₀, r₁, hr₁, hne⟩ := Finset.one_lt_card.mp hpos
      have hdiff : ∃ i₁ : Fin rk, ev i₁ r₀ ≠ ev i₁ r₁ := by
        by_contra hcon
        push Not at hcon
        exact hne (hev_inj hcon)
      obtain ⟨i₁, hi₁⟩ := hdiff
      let lam0 : K := ev i₁ r₀
      have hy : ⁅H i₁, h0 + ∑ r ∈ B, c r • R r⁆ -
          lam0 • (h0 + ∑ r ∈ B, c r • R r) ∈ S :=
        S.sub_mem (hS i₁ _ hc) (S.smul_mem lam0 hc)
      let c' : Fin m → K := fun r => c r * ((ev i₁ r : K) - lam0)
      have hy_eq : ⁅H i₁, h0 + ∑ r ∈ B, c r • R r⁆ -
          lam0 • (h0 + ∑ r ∈ B, c r • R r) =
          (-lam0) • h0 + ∑ r ∈ B.erase r₀, c' r • R r := by
        rw [lie_add, hKillH h0 hh0 i₁, zero_add, lie_sum, smul_add, Finset.smul_sum]
        have h1 : ∑ r ∈ B, ⁅H i₁, c r • R r⁆ =
            ∑ r ∈ B, (c r * (ev i₁ r : K)) • R r := by
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [lie_smul, hHR, smul_smul]
        rw [h1]
        have h2 : ∑ r ∈ B, (c r * (ev i₁ r : K)) • R r -
            (lam0 • h0 + ∑ r ∈ B, lam0 • (c r • R r)) =
            (-lam0) • h0 + ∑ r ∈ B, c' r • R r := by
          rw [sub_eq_add_neg, neg_add, ← neg_smul lam0 h0,
            add_comm (-lam0 • h0) (-(∑ r ∈ B, lam0 • (c r • R r))), ← add_assoc,
            add_comm (∑ r ∈ B, (c r * (ev i₁ r : K)) • R r +
              -(∑ r ∈ B, lam0 • (c r • R r))) ((-lam0) • h0)]
          congr 1
          rw [← sub_eq_add_neg, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun r _ => ?_
          dsimp [c']
          rw [smul_smul, ← sub_smul]
          congr 1; ring
        rw [h2, ← Finset.add_sum_erase B (fun r => c' r • R r) hr₀]
        have hc'0 : c' r₀ = 0 := by simp [c', lam0]
        rw [hc'0, zero_smul, zero_add]
      rw [hy_eq] at hy
      have hcard0 : (B.erase r₀).card = n := by rw [Finset.card_erase_of_mem hr₀, hcard]; simp
      have ih0 := ih (B.erase r₀) ((-lam0) • h0) (Submodule.smul_mem _ (-lam0) hh0) hcard0 c' hy
      have hr₁_erase : r₁ ∈ B.erase r₀ := Finset.mem_erase.mpr ⟨hne.symm, hr₁⟩
      have hc'r₁ := ih0.2 r₁ hr₁_erase
      have hlam_ne : ((ev i₁ r₁ : K) - lam0) ≠ 0 := by
        intro heq
        apply hi₁
        exact (Int.cast_injective (sub_eq_zero.mp heq)).symm
      have hr₁_mem : c r₁ • R r₁ ∈ S := by
        have hs := S.smul_mem ((ev i₁ r₁ : K) - lam0)⁻¹ hc'r₁
        dsimp [c'] at hs
        rw [smul_smul, mul_comm (c r₁), ← mul_assoc, inv_mul_cancel₀ hlam_ne, one_mul] at hs
        exact hs
      have hx_erase : h0 + ∑ r ∈ B.erase r₁, c r • R r ∈ S := by
        have hsub := S.sub_mem hc hr₁_mem
        have hs_eq : (h0 + ∑ r ∈ B, c r • R r) - c r₁ • R r₁ =
            h0 + ∑ r ∈ B.erase r₁, c r • R r := by
          rw [← Finset.add_sum_erase B _ hr₁]
          abel
        rwa [hs_eq] at hsub
      have hcard1 : (B.erase r₁).card = n := by rw [Finset.card_erase_of_mem hr₁, hcard]; simp
      have ih1 := ih (B.erase r₁) h0 hh0 hcard1 c hx_erase
      refine ⟨ih1.1, fun r hr => ?_⟩
      by_cases heq : r = r₁
      · subst heq; exact hr₁_mem
      · exact ih1.2 r (Finset.mem_erase.mpr ⟨heq, hr⟩)

/-- Bundled split Chevalley presentation over a field `K` of characteristic zero. -/
structure SplitChevalleyData (K L : Type*) [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
    (rk m : ℕ) where
  rk_pos : 0 < rk
  H : Fin rk → L
  E : Fin rk → L
  F : Fin rk → L
  R : Fin m → L
  basis : Module.Basis (Fin rk ⊕ Fin m) K L
  basis_inl : ∀ i, basis (Sum.inl i) = H i
  basis_inr : ∀ r, basis (Sum.inr r) = R r
  ev : Fin rk → Fin m → ℤ
  C : Matrix (Fin rk) (Fin rk) ℤ
  C_inv : Matrix (Fin rk) (Fin rk) ℤ
  detC : ℤ
  detC_ne_zero : detC ≠ 0
  C_inv_mul_transpose : ∀ i k : Fin rk, ∑ j : Fin rk, C_inv i j * C k j = if i = k then detC else 0
  C_diag : ∀ i : Fin rk, C i i = 2
  eIdx : Fin rk → Fin m
  fIdx : Fin rk → Fin m
  eSgn : Fin rk → ℤ
  fSgn : Fin rk → ℤ
  eSgn_ne_zero : ∀ i, eSgn i ≠ 0
  fSgn_ne_zero : ∀ i, fSgn i ≠ 0
  e_eq : ∀ i, E i = (eSgn i : K) • R (eIdx i)
  f_eq : ∀ i, F i = (fSgn i : K) • R (fIdx i)
  hiIdx : Fin m
  ht : Fin m → ℤ
  maxHt : ℕ
  ht_bounds : ∀ r, ht r ≠ 0 ∧ -(maxHt : ℤ) ≤ ht r ∧ ht r ≤ (maxHt : ℤ)
  ht_hi : ht hiIdx = (maxHt : ℤ)
  ht_eSimple : ∀ i, ht (eIdx i) = 1
  ht_fSimple : ∀ i, ht (fIdx i) = -1
  negHeight_negOne_eq_fSimple : ∀ r, ht r = -1 → ∃ i, r = fIdx i
  posRaise : Fin m → Fin rk × Fin m × ℤ
  negRaise : Fin m → Fin rk × Fin m × ℤ
  posLower : Fin m → Option (Fin rk × Fin m × ℤ)
  negLower : Fin m → Option (Fin rk × Fin m × ℤ)
  bracket_HH : ∀ i j, ⁅H i, H j⁆ = 0
  bracket_HR : ∀ i r, ⁅H i, R r⁆ = (ev i r : K) • R r
  bracket_HE : ∀ i j, ⁅H i, E j⁆ = (C i j : K) • E j
  bracket_HF_same : ∀ i, ⁅H i, F i⁆ = (-2 : K) • F i
  bracket_EF_same : ∀ i, ⁅E i, F i⁆ = H i
  ev_ne_zero : ∀ r, ∃ i, ev i r ≠ 0
  ev_inj : ∀ {r₁ r₂}, (∀ i, ev i r₁ = ev i r₂) → r₁ = r₂
  posRaise_spec : ∀ r, 0 < ht r → r ≠ hiIdx →
    let st := posRaise r
    ⁅E st.1, R r⁆ = (st.2.2 : K) • R st.2.1 ∧ ht r < ht st.2.1 ∧ st.2.2 ≠ 0
  negRaise_spec : ∀ r, ht r < -1 →
    let st := negRaise r
    ⁅E st.1, R r⁆ = (st.2.2 : K) • R st.2.1 ∧ ht r < ht st.2.1 ∧ ht st.2.1 < 0 ∧ st.2.2 ≠ 0
  posLower_spec : ∀ r, 0 < ht r →
    (posLower r = none → r = hiIdx) ∧
    (∀ st, posLower r = some st →
      ⁅F st.1, R st.2.1⁆ = (st.2.2 : K) • R r ∧ ht r < ht st.2.1 ∧ 0 < ht st.2.1 ∧ st.2.2 ≠ 0)
  negLower_spec : ∀ r, ht r < 0 →
    (negLower r = none → ∃ i, r = fIdx i) ∧
    (∀ st, negLower r = some st →
      ⁅F st.1, R st.2.1⁆ = (st.2.2 : K) • R r ∧ ht r < ht st.2.1 ∧ ht st.2.1 < 0 ∧ st.2.2 ≠ 0)

namespace SplitChevalleyData

section Simplicity

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] {rk m : ℕ}
variable (D : SplitChevalleyData K L rk m)

private theorem smul_int_mem_ideal {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
    (I : LieIdeal K L) {c : ℤ} (hc : c ≠ 0) {x : L}
    (hx : (c : K) • x ∈ I) : x ∈ I := by
  have hne : (c : K) ≠ 0 := Int.cast_ne_zero.mpr hc
  have hsm := I.smul_mem (c : K)⁻¹ hx
  rw [smul_smul, inv_mul_cancel₀ hne, one_smul] at hsm
  exact hsm

private theorem pos_root_mem_ideal_imp_highest (I : LieIdeal K L) :
    ∀ n : ℕ, ∀ r : Fin m, 0 < D.ht r → ((D.maxHt : ℤ) - D.ht r).toNat ≤ n →
      D.R r ∈ I → D.R D.hiIdx ∈ I := by
  intro n
  induction n with
  | zero =>
    intro r hpos hle hrI
    have hhi : D.ht r = (D.maxHt : ℤ) := by
      have hb := (D.ht_bounds r).2.2
      omega
    by_cases heq : r = D.hiIdx
    · subst heq; exact hrI
    · exfalso
      have hst := D.posRaise_spec r hpos heq
      have hb := (D.ht_bounds (D.posRaise r).2.1).2.2
      omega
  | succ n ih =>
    intro r hpos hle hrI
    by_cases heq : r = D.hiIdx
    · subst heq; exact hrI
    · have hst := D.posRaise_spec r hpos heq
      have hbr : ⁅D.E (D.posRaise r).1, D.R r⁆ ∈ I := I.lie_mem hrI
      rw [hst.1] at hbr
      have hnext : D.R (D.posRaise r).2.1 ∈ I := smul_int_mem_ideal I hst.2.2 hbr
      have hb := (D.ht_bounds (D.posRaise r).2.1).2.2
      exact ih (D.posRaise r).2.1 (by omega) (by omega) hnext

private theorem highest_mem_ideal_imp_pos_roots (I : LieIdeal K L)
    (hhi : D.R D.hiIdx ∈ I) :
    ∀ n : ℕ, ∀ r : Fin m, 0 < D.ht r → ((D.maxHt : ℤ) - D.ht r).toNat ≤ n →
      D.R r ∈ I := by
  intro n
  induction n with
  | zero =>
    intro r hpos hle
    have hmax : D.ht r = (D.maxHt : ℤ) := by
      have hb := (D.ht_bounds r).2.2
      omega
    have hspec := D.posLower_spec r hpos
    cases hst : D.posLower r with
    | none => rw [hspec.1 hst]; exact hhi
    | some st =>
      exfalso
      have hlt := (hspec.2 st hst).2.1
      have hb := (D.ht_bounds st.2.1).2.2
      omega
  | succ n ih =>
    intro r hpos hle
    have hspec := D.posLower_spec r hpos
    cases hst : D.posLower r with
    | none => rw [hspec.1 hst]; exact hhi
    | some st =>
      have hm := hspec.2 st hst
      have hb := (D.ht_bounds st.2.1).2.2
      have hpar : D.R st.2.1 ∈ I := ih st.2.1 hm.2.2.1 (by omega)
      have hbr : ⁅D.F st.1, D.R st.2.1⁆ ∈ I := I.lie_mem hpar
      rw [hm.1] at hbr
      exact smul_int_mem_ideal I hm.2.2.2 hbr

private theorem highest_mem_ideal_imp_top (I : LieIdeal K L)
    (hhi : D.R D.hiIdx ∈ I) : I = ⊤ := by
  have hpos_all : ∀ r : Fin m, 0 < D.ht r → D.R r ∈ I := by
    intro r hr
    exact D.highest_mem_ideal_imp_pos_roots I hhi D.maxHt r hr (by
      have hb := (D.ht_bounds r).2.1; omega)
  have he_mem : ∀ i : Fin rk, D.E i ∈ I := by
    intro i
    rw [D.e_eq i]
    exact I.smul_mem _ (hpos_all (D.eIdx i) (by rw [D.ht_eSimple i]; norm_num))
  have hh_mem : ∀ i : Fin rk, D.H i ∈ I := by
    intro i
    rw [← D.bracket_EF_same i, ← lie_skew]
    exact I.neg_mem (I.lie_mem (he_mem i))
  have hf_mem : ∀ i : Fin rk, D.F i ∈ I := by
    intro i
    have hbr : ⁅D.H i, D.F i⁆ ∈ I := by
      rw [← lie_skew]
      exact I.neg_mem (I.lie_mem (hh_mem i))
    rw [D.bracket_HF_same] at hbr
    have hsm := I.smul_mem (-2 : K)⁻¹ hbr
    rw [smul_smul, inv_mul_cancel₀ (by norm_num : (-2 : K) ≠ 0), one_smul] at hsm
    exact hsm
  have hf_root_mem : ∀ i : Fin rk, D.R (D.fIdx i) ∈ I := by
    intro i
    have hfi := hf_mem i
    rw [D.f_eq i] at hfi
    exact smul_int_mem_ideal I (D.fSgn_ne_zero i) hfi
  have hneg_all : ∀ n : ℕ, ∀ r : Fin m, D.ht r < 0 → (D.ht r).natAbs ≤ n → D.R r ∈ I := by
    intro n
    induction n with
    | zero =>
      intro r hneg hle
      omega
    | succ n ih =>
      intro r hneg hle
      have hspec := D.negLower_spec r hneg
      cases hst : D.negLower r with
      | none =>
        obtain ⟨i, rfl⟩ := hspec.1 hst
        exact hf_root_mem i
      | some st =>
        have hm := hspec.2 st hst
        have hpar : D.R st.2.1 ∈ I := ih st.2.1 hm.2.2.1 (by omega)
        have hbr : ⁅D.F st.1, D.R st.2.1⁆ ∈ I := I.lie_mem hpar
        rw [hm.1] at hbr
        exact smul_int_mem_ideal I hm.2.2.2 hbr
  have hall_roots : ∀ r : Fin m, D.R r ∈ I := by
    intro r
    have hnz := (D.ht_bounds r).1
    rcases lt_or_gt_of_ne hnz with hneg | hpos
    · exact hneg_all D.maxHt r hneg (by have hb := (D.ht_bounds r).2.1; omega)
    · exact hpos_all r hpos
  rw [eq_top_iff]
  intro x _
  have hrep := Module.Basis.sum_repr D.basis x
  rw [← hrep, Fintype.sum_sum_type]
  refine I.add_mem (I.sum_mem fun i _ => I.smul_mem _ ?_)
    (I.sum_mem fun r _ => I.smul_mem _ ?_)
  · rw [D.basis_inl i]; exact hh_mem i
  · rw [D.basis_inr r]; exact hall_roots r

private theorem cartan_ne_zero_mem_ideal_imp_highest (I : LieIdeal K L)
    (u : L) (hu : u ∈ Submodule.span K (Set.range D.H)) (hne : u ≠ 0) (hI : u ∈ I) :
    D.R D.hiIdx ∈ I := by
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hu
  have ha_ne : ∃ j : Fin rk, ∑ i : Fin rk, a i * (D.C i j : K) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have ha0 : ∀ i : Fin rk, a i = 0 := by
      intro i
      have hsum0 : ∑ j : Fin rk, (D.C_inv i j : K) * (∑ k : Fin rk, a k * (D.C k j : K)) = 0 := by
        refine Finset.sum_eq_zero fun j _ => ?_
        rw [hcon j, mul_zero]
      have hswap : ∑ j : Fin rk, (D.C_inv i j : K) * (∑ k : Fin rk, a k * (D.C k j : K)) =
          a i * (D.detC : K) := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        have hinner : ∀ k : Fin rk,
            ∑ j : Fin rk, (D.C_inv i j : K) * (a k * (D.C k j : K)) =
              a k * ((if i = k then D.detC else 0 : ℤ) : K) := by
          intro k
          have h1 : ∑ j : Fin rk, (D.C_inv i j : K) * (a k * (D.C k j : K)) =
              a k * ∑ j : Fin rk, ((D.C_inv i j * D.C k j : ℤ) : K) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            push_cast; ring
          rw [h1, ← Int.cast_sum, D.C_inv_mul_transpose i k]
        simp_rw [hinner]
        rw [Finset.sum_eq_single i]
        · simp
        · intro k _ hki
          simp [hki.symm]
        · intro hi; exact absurd (Finset.mem_univ i) hi
      rw [hswap] at hsum0
      exact (mul_eq_zero.mp hsum0).resolve_right (Int.cast_ne_zero.mpr D.detC_ne_zero)
    exact hne (Finset.sum_eq_zero fun i _ => by rw [ha0 i, zero_smul])
  obtain ⟨j, hj⟩ := ha_ne
  have hbr : ⁅∑ i : Fin rk, a i • D.H i, D.E j⁆ ∈ I := by
    rw [← lie_skew]
    exact I.neg_mem (I.lie_mem hI)
  have heq : ⁅∑ i : Fin rk, a i • D.H i, D.E j⁆ =
      (∑ i : Fin rk, a i * (D.C i j : K)) • D.E j := by
    rw [sum_lie]
    simp only [smul_lie, D.bracket_HE, smul_smul, Finset.sum_smul]
  rw [heq] at hbr
  have hej : D.E j ∈ I := by
    have hs := I.smul_mem (∑ i : Fin rk, a i * (D.C i j : K))⁻¹ hbr
    rw [smul_smul, inv_mul_cancel₀ hj, one_smul] at hs
    exact hs
  rw [D.e_eq j] at hej
  have hrj : D.R (D.eIdx j) ∈ I := smul_int_mem_ideal I (D.eSgn_ne_zero j) hej
  exact D.pos_root_mem_ideal_imp_highest I D.maxHt (D.eIdx j)
    (by rw [D.ht_eSimple j]; norm_num)
    (by have hb := (D.ht_bounds (D.eIdx j)).2.2; rw [D.ht_eSimple j] at hb ⊢; omega)
    hrj

private theorem neg_root_mem_ideal_imp_highest (I : LieIdeal K L) :
    ∀ n : ℕ, ∀ r : Fin m, D.ht r < 0 → (D.ht r).natAbs ≤ n →
      D.R r ∈ I → D.R D.hiIdx ∈ I := by
  intro n
  induction n with
  | zero =>
    intro r hneg hle
    omega
  | succ n ih =>
    intro r hneg hle hrI
    by_cases h1 : D.ht r = -1
    · obtain ⟨i, rfl⟩ := D.negHeight_negOne_eq_fSimple r h1
      have hfi : D.F i ∈ I := by
        rw [D.f_eq i]
        exact I.smul_mem _ hrI
      have hhi : D.H i ∈ I := by
        rw [← D.bracket_EF_same i]
        exact I.lie_mem hfi
      have hne : D.H i ≠ 0 := by
        rw [← D.basis_inl i]
        exact D.basis.ne_zero (Sum.inl i)
      exact D.cartan_ne_zero_mem_ideal_imp_highest I (D.H i)
        (Submodule.subset_span ⟨i, rfl⟩) hne hhi
    · have hlt : D.ht r < -1 := by omega
      have hst := D.negRaise_spec r hlt
      have hbr : ⁅D.E (D.negRaise r).1, D.R r⁆ ∈ I := I.lie_mem hrI
      rw [hst.1] at hbr
      have hnext : D.R (D.negRaise r).2.1 ∈ I := smul_int_mem_ideal I hst.2.2.2 hbr
      exact ih (D.negRaise r).2.1 hst.2.2.1 (by omega) hnext

private theorem root_mem_ideal_imp_highest (I : LieIdeal K L)
    (r : Fin m) (hr : D.R r ∈ I) : D.R D.hiIdx ∈ I := by
  have hnz := (D.ht_bounds r).1
  rcases lt_or_gt_of_ne hnz with hneg | hpos
  · exact D.neg_root_mem_ideal_imp_highest I D.maxHt r hneg
      (by have hb := (D.ht_bounds r).2.1; omega) hr
  · exact D.pos_root_mem_ideal_imp_highest I D.maxHt r hpos
      (by have hb := (D.ht_bounds r).2.1; omega) hr

/-- Any split Chevalley Lie algebra over a field `K` of characteristic `0` is simple. -/
theorem isSimple (D : SplitChevalleyData K L rk m) : LieAlgebra.IsSimple K L where
  eq_bot_or_eq_top I := by
    by_cases hbot : I = ⊥
    · exact Or.inl hbot
    · right
      have hne : ∃ x ∈ I, x ≠ 0 := by
        by_contra hall
        push Not at hall
        apply hbot
        rw [eq_bot_iff]
        intro x hx
        exact hall x hx
      obtain ⟨x, hxI, hxne⟩ := hne
      have hrep := Module.Basis.sum_repr D.basis x
      rw [Fintype.sum_sum_type] at hrep
      simp_rw [D.basis_inl, D.basis_inr] at hrep
      have hhpart : (∑ i : Fin rk, D.basis.repr x (Sum.inl i) • D.H i) ∈
          Submodule.span K (Set.range D.H) :=
        Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
      have hkill := cartan_weight_kill_mem_generic D.H D.R D.ev D.bracket_HH D.bracket_HR
        D.ev_ne_zero D.ev_inj I.toSubmodule (fun i y hy => I.lie_mem hy)
        Finset.univ (∑ i : Fin rk, D.basis.repr x (Sum.inl i) • D.H i) hhpart
        (fun r => D.basis.repr x (Sum.inr r)) (by rw [hrep]; exact hxI)
      by_cases hhp0 : (∑ i : Fin rk, D.basis.repr x (Sum.inl i) • D.H i) = 0
      · have hex : ∃ r : Fin m, D.basis.repr x (Sum.inr r) ≠ 0 := by
          by_contra hall
          push Not at hall
          have hs0 : (∑ r : Fin m, D.basis.repr x (Sum.inr r) • D.R r) = 0 :=
            Finset.sum_eq_zero fun r _ => by rw [hall r, zero_smul]
          apply hxne
          rw [← hrep, hhp0, hs0, add_zero]
        obtain ⟨r, hr⟩ := hex
        have hrI : D.R r ∈ I := by
          have hs := I.smul_mem (D.basis.repr x (Sum.inr r))⁻¹ (hkill.2 r (Finset.mem_univ r))
          rw [smul_smul, inv_mul_cancel₀ hr, one_smul] at hs
          exact hs
        exact D.highest_mem_ideal_imp_top I (D.root_mem_ideal_imp_highest I r hrI)
      · exact D.highest_mem_ideal_imp_top I
          (D.cartan_ne_zero_mem_ideal_imp_highest I
            (∑ i : Fin rk, D.basis.repr x (Sum.inl i) • D.H i) hhpart hhp0 hkill.1)
  non_abelian := by
    intro hab
    let i₀ : Fin rk := ⟨0, D.rk_pos⟩
    have h0 := hab.trivial (D.H i₀) (D.E i₀)
    rw [D.bracket_HE, D.C_diag i₀, D.e_eq i₀, smul_smul] at h0
    have hne : D.R (D.eIdx i₀) ≠ 0 := by
      rw [← D.basis_inr (D.eIdx i₀)]
      exact D.basis.ne_zero (Sum.inr (D.eIdx i₀))
    have hsm := (smul_eq_zero.mp h0).resolve_right hne
    have h2 : ((2 : ℤ) : K) ≠ 0 := by norm_num
    have hsgn : (D.eSgn i₀ : K) ≠ 0 := Int.cast_ne_zero.mpr (D.eSgn_ne_zero i₀)
    exact mul_ne_zero h2 hsgn hsm

end Simplicity

section ExtendScalars

/-- Base change of a real `SplitChevalleyData` to any characteristic-`0` `ℝ`-algebra field `K`. -/
def extendScalars {L : Type*} [LieRing L] [LieAlgebra ℝ L] {rk m : ℕ}
    (D : SplitChevalleyData ℝ L rk m)
    (K : Type*) [Field K] [CharZero K] [Algebra ℝ K] :
    SplitChevalleyData K (K ⊗[ℝ] L) rk m where
  rk_pos := D.rk_pos
  H i := (1 : K) ⊗ₜ[ℝ] D.H i
  E i := (1 : K) ⊗ₜ[ℝ] D.E i
  F i := (1 : K) ⊗ₜ[ℝ] D.F i
  R r := (1 : K) ⊗ₜ[ℝ] D.R r
  basis := D.basis.baseChange K
  basis_inl i := by simp [D.basis_inl i]
  basis_inr r := by simp [D.basis_inr r]
  ev := D.ev
  C := D.C
  C_inv := D.C_inv
  detC := D.detC
  detC_ne_zero := D.detC_ne_zero
  C_inv_mul_transpose := D.C_inv_mul_transpose
  C_diag := D.C_diag
  eIdx := D.eIdx
  fIdx := D.fIdx
  eSgn := D.eSgn
  fSgn := D.fSgn
  eSgn_ne_zero := D.eSgn_ne_zero
  fSgn_ne_zero := D.fSgn_ne_zero
  e_eq i := by
    rw [D.e_eq i, TensorProduct.tmul_smul, ← IsScalarTower.algebraMap_smul K (D.eSgn i : ℝ),
      map_intCast]
  f_eq i := by
    rw [D.f_eq i, TensorProduct.tmul_smul, ← IsScalarTower.algebraMap_smul K (D.fSgn i : ℝ),
      map_intCast]
  hiIdx := D.hiIdx
  ht := D.ht
  maxHt := D.maxHt
  ht_bounds := D.ht_bounds
  ht_hi := D.ht_hi
  ht_eSimple := D.ht_eSimple
  ht_fSimple := D.ht_fSimple
  negHeight_negOne_eq_fSimple := D.negHeight_negOne_eq_fSimple
  posRaise := D.posRaise
  negRaise := D.negRaise
  posLower := D.posLower
  negLower := D.negLower
  bracket_HH i j := by
    rw [LieAlgebra.ExtendScalars.bracket_tmul, D.bracket_HH, TensorProduct.tmul_zero]
  bracket_HR i r := by
    rw [LieAlgebra.ExtendScalars.bracket_tmul, one_mul, D.bracket_HR,
      TensorProduct.tmul_smul, ← IsScalarTower.algebraMap_smul K (D.ev i r : ℝ), map_intCast]
  bracket_HE i j := by
    rw [LieAlgebra.ExtendScalars.bracket_tmul, one_mul, D.bracket_HE,
      TensorProduct.tmul_smul, ← IsScalarTower.algebraMap_smul K (D.C i j : ℝ), map_intCast]
  bracket_HF_same i := by
    rw [LieAlgebra.ExtendScalars.bracket_tmul, one_mul, D.bracket_HF_same,
      TensorProduct.tmul_smul, ← IsScalarTower.algebraMap_smul K (-2 : ℝ),
      map_neg, map_ofNat]
  bracket_EF_same i := by
    rw [LieAlgebra.ExtendScalars.bracket_tmul, one_mul, D.bracket_EF_same]
  ev_ne_zero := D.ev_ne_zero
  ev_inj := D.ev_inj
  posRaise_spec r hpos hne := by
    obtain ⟨hbr, hlt, hnz⟩ := D.posRaise_spec r hpos hne
    refine ⟨?_, hlt, hnz⟩
    rw [LieAlgebra.ExtendScalars.bracket_tmul, one_mul, hbr,
      TensorProduct.tmul_smul, ← IsScalarTower.algebraMap_smul K ((D.posRaise r).2.2 : ℝ),
      map_intCast]
  negRaise_spec r hneg := by
    obtain ⟨hbr, hlt1, hlt2, hnz⟩ := D.negRaise_spec r hneg
    refine ⟨?_, hlt1, hlt2, hnz⟩
    rw [LieAlgebra.ExtendScalars.bracket_tmul, one_mul, hbr,
      TensorProduct.tmul_smul, ← IsScalarTower.algebraMap_smul K ((D.negRaise r).2.2 : ℝ),
      map_intCast]
  posLower_spec r hpos := by
    obtain ⟨hnone, hsome⟩ := D.posLower_spec r hpos
    refine ⟨hnone, fun st hst => ?_⟩
    obtain ⟨hbr, hlt, hp, hnz⟩ := hsome st hst
    refine ⟨?_, hlt, hp, hnz⟩
    rw [LieAlgebra.ExtendScalars.bracket_tmul, one_mul, hbr,
      TensorProduct.tmul_smul, ← IsScalarTower.algebraMap_smul K (st.2.2 : ℝ), map_intCast]
  negLower_spec r hneg := by
    obtain ⟨hnone, hsome⟩ := D.negLower_spec r hneg
    refine ⟨hnone, fun st hst => ?_⟩
    obtain ⟨hbr, hlt, hn, hnz⟩ := hsome st hst
    refine ⟨?_, hlt, hn, hnz⟩
    rw [LieAlgebra.ExtendScalars.bracket_tmul, one_mul, hbr,
      TensorProduct.tmul_smul, ← IsScalarTower.algebraMap_smul K (st.2.2 : ℝ), map_intCast]

end ExtendScalars

end SplitChevalleyData

end SplitChevalleyEngine

section F4ChevalleyAndSimplicity

open H3Zorn
open InfoGeometry.Canonical.H3ZornF4PeirceTrialitySplit

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

private instance : Module.Finite ℝ H3ZornF4Derivations :=
  FiniteDimensional.of_finrank_pos (by rw [finrank_H3ZornF4Derivations]; decide)

private def f4D4Pair (k : Fin 24) : Fin 8 × Fin 8 :=
  match k.val with
  | 0 => (0, 1) | 1 => (0, 2) | 2 => (0, 3) | 3 => (0, 4) | 4 => (0, 5) | 5 => (0, 6)
  | 6 => (1, 2) | 7 => (1, 3) | 8 => (1, 5) | 9 => (1, 6) | 10 => (1, 7)
  | 11 => (2, 3) | 12 => (2, 4) | 13 => (2, 6) | 14 => (2, 7)
  | 15 => (3, 4) | 16 => (3, 5) | 17 => (3, 7)
  | 18 => (4, 5) | 19 => (4, 6) | 20 => (4, 7)
  | 21 => (5, 6) | 22 => (5, 7) | _ => (6, 7)

/-- The 48 root operators of `𝔣₄(4)` inside `H3ZornF4Derivations`, obtained by folding
the 72 `E₆` root operators of `H3ZornE6RootSystem`. -/
def f4RootVec (r : Fin 48) : H3ZornF4Derivations :=
  if h24 : r.val < 24 then
    let p := f4D4Pair ⟨r.val, h24⟩
    (2 : ℝ) • h3ZornJordanInnerDerivation (h3_off₁₂ p.1) (h3_off₁₂ p.2)
  else
    let k := r.val - 24
    if hk8 : k < 8 then
      (4 : ℝ) • h3ZornJordanInnerDerivation h3_diag₁ (h3_off₁₂ ⟨k, hk8⟩)
    else if hk16 : k < 16 then
      (4 : ℝ) • h3ZornJordanInnerDerivation h3_diag₂ (h3_off₂₃ ⟨k - 8, by omega⟩)
    else
      (4 : ℝ) • h3ZornJordanInnerDerivation h3_diag₃ (h3_off₃₁ ⟨k - 16, by omega⟩)

/-- Normalized 27×27 sparse integer matrices for the 48 `F₄` root operators. -/
def f4RootSparse (r : Fin 48) : SparseMat27 :=
  match r.val with
  | 0 => [(3, 7, -1), (4, 10, -1), (16, 14, -1), (17, 13, 1), (20, 19, 1), (26, 23, 1)]
  | 1 => [(3, 8, -1), (5, 10, -1), (15, 14, 1), (17, 12, -1), (21, 19, 1), (26, 24, 1)]
  | 2 => [(3, 9, -1), (6, 10, -1), (15, 13, -1), (16, 12, 1), (22, 19, 1), (26, 25, 1)]
  | 3 => [(3, 4, -1), (7, 10, -1), (15, 11, 1), (18, 12, 1), (21, 25, -1), (22, 24, 1)]
  | 4 => [(3, 5, -1), (8, 10, -1), (16, 11, 1), (18, 13, 1), (20, 25, 1), (22, 23, -1)]
  | 5 => [(3, 6, -1), (9, 10, -1), (17, 11, 1), (18, 14, 1), (20, 24, -1), (21, 23, 1)]
  | 6 => [(4, 8, -1), (5, 7, 1), (11, 14, -1), (17, 18, -1), (25, 19, 1), (26, 22, 1)]
  | 7 => [(4, 9, -1), (6, 7, 1), (11, 13, 1), (16, 18, 1), (24, 19, -1), (26, 21, -1)]
  | 8 => [(4, 5, -1), (8, 7, 1), (12, 13, -1), (16, 15, 1), (20, 21, -1), (24, 23, 1)]
  | 9 => [(4, 6, -1), (9, 7, 1), (12, 14, -1), (17, 15, 1), (20, 22, -1), (25, 23, 1)]
  | 10 => [(4, 3, 1), (10, 7, 1), (11, 15, -1), (12, 18, -1), (24, 22, -1), (25, 21, 1)]
  | 11 => [(5, 9, -1), (6, 8, 1), (11, 12, -1), (15, 18, -1), (23, 19, 1), (26, 20, 1)]
  | 12 => [(5, 4, -1), (7, 8, 1), (13, 12, -1), (15, 16, 1), (21, 20, -1), (23, 24, 1)]
  | 13 => [(5, 6, -1), (9, 8, 1), (13, 14, -1), (17, 16, 1), (21, 22, -1), (25, 24, 1)]
  | 14 => [(5, 3, 1), (10, 8, 1), (11, 16, -1), (13, 18, -1), (23, 22, 1), (25, 20, -1)]
  | 15 => [(6, 4, -1), (7, 9, 1), (14, 12, -1), (15, 17, 1), (22, 20, -1), (23, 25, 1)]
  | 16 => [(6, 5, -1), (8, 9, 1), (14, 13, -1), (16, 17, 1), (22, 21, -1), (24, 25, 1)]
  | 17 => [(6, 3, 1), (10, 9, 1), (11, 17, -1), (14, 18, -1), (23, 21, -1), (24, 20, 1)]
  | 18 => [(7, 5, -1), (8, 4, 1), (14, 11, 1), (18, 17, 1), (19, 25, -1), (22, 26, -1)]
  | 19 => [(7, 6, -1), (9, 4, 1), (13, 11, -1), (18, 16, -1), (19, 24, 1), (21, 26, 1)]
  | 20 => [(7, 3, 1), (10, 4, 1), (13, 17, -1), (14, 16, 1), (19, 20, -1), (23, 26, -1)]
  | 21 => [(8, 6, -1), (9, 5, 1), (12, 11, 1), (18, 15, 1), (19, 23, -1), (20, 26, -1)]
  | 22 => [(8, 3, 1), (10, 5, 1), (12, 17, 1), (14, 15, -1), (19, 21, -1), (24, 26, -1)]
  | 23 => [(9, 3, 1), (10, 6, 1), (12, 16, -1), (13, 15, 1), (19, 22, -1), (25, 26, -1)]
  | 24 => [(0, 10, 1), (1, 10, -1), (3, 0, -1), (3, 1, 1), (15, 23, 1), (16, 24, 1), (17, 25, 1), (18, 19, -1), (20, 12, -1), (21, 13, -1), (22, 14, -1), (26, 11, 1)]
  | 25 => [(0, 7, -1), (1, 7, 1), (4, 0, -1), (4, 1, 1), (11, 23, -1), (12, 19, 1), (16, 22, 1), (17, 21, -1), (20, 18, -1), (24, 14, 1), (25, 13, -1), (26, 15, 1)]
  | 26 => [(0, 8, -1), (1, 8, 1), (5, 0, -1), (5, 1, 1), (11, 24, -1), (13, 19, 1), (15, 22, -1), (17, 20, 1), (21, 18, -1), (23, 14, -1), (25, 12, 1), (26, 16, 1)]
  | 27 => [(0, 9, -1), (1, 9, 1), (6, 0, -1), (6, 1, 1), (11, 25, -1), (14, 19, 1), (15, 21, 1), (16, 20, -1), (22, 18, -1), (23, 13, 1), (24, 12, -1), (26, 17, 1)]
  | 28 => [(0, 4, -1), (1, 4, 1), (7, 0, -1), (7, 1, 1), (13, 25, -1), (14, 24, 1), (15, 26, 1), (18, 20, -1), (19, 12, 1), (21, 17, -1), (22, 16, 1), (23, 11, -1)]
  | 29 => [(0, 5, -1), (1, 5, 1), (8, 0, -1), (8, 1, 1), (12, 25, 1), (14, 23, -1), (16, 26, 1), (18, 21, -1), (19, 13, 1), (20, 17, 1), (22, 15, -1), (24, 11, -1)]
  | 30 => [(0, 6, -1), (1, 6, 1), (9, 0, -1), (9, 1, 1), (12, 24, -1), (13, 23, 1), (17, 26, 1), (18, 22, -1), (19, 14, 1), (20, 16, -1), (21, 15, 1), (25, 11, -1)]
  | 31 => [(0, 3, 1), (1, 3, -1), (10, 0, -1), (10, 1, 1), (11, 26, -1), (12, 20, 1), (13, 21, 1), (14, 22, 1), (19, 18, 1), (23, 15, -1), (24, 16, -1), (25, 17, -1)]
  | 32 => [(1, 18, 1), (2, 18, -1), (4, 20, -1), (5, 21, -1), (6, 22, -1), (10, 19, 1), (11, 1, -1), (11, 2, 1), (23, 7, 1), (24, 8, 1), (25, 9, 1), (26, 3, -1)]
  | 33 => [(1, 15, -1), (2, 15, 1), (4, 26, -1), (8, 22, 1), (9, 21, -1), (10, 23, 1), (12, 1, -1), (12, 2, 1), (19, 7, -1), (20, 3, 1), (24, 6, 1), (25, 5, -1)]
  | 34 => [(1, 16, -1), (2, 16, 1), (5, 26, -1), (7, 22, -1), (9, 20, 1), (10, 24, 1), (13, 1, -1), (13, 2, 1), (19, 8, -1), (21, 3, 1), (23, 6, -1), (25, 4, 1)]
  | 35 => [(1, 17, -1), (2, 17, 1), (6, 26, -1), (7, 21, 1), (8, 20, -1), (10, 25, 1), (14, 1, -1), (14, 2, 1), (19, 9, -1), (22, 3, 1), (23, 5, 1), (24, 4, -1)]
  | 36 => [(1, 12, -1), (2, 12, 1), (3, 20, 1), (5, 25, -1), (6, 24, 1), (7, 19, -1), (15, 1, -1), (15, 2, 1), (21, 9, -1), (22, 8, 1), (23, 10, 1), (26, 4, -1)]
  | 37 => [(1, 13, -1), (2, 13, 1), (3, 21, 1), (4, 25, 1), (6, 23, -1), (8, 19, -1), (16, 1, -1), (16, 2, 1), (20, 9, 1), (22, 7, -1), (24, 10, 1), (26, 5, -1)]
  | 38 => [(1, 14, -1), (2, 14, 1), (3, 22, 1), (4, 24, -1), (5, 23, 1), (9, 19, -1), (17, 1, -1), (17, 2, 1), (20, 8, -1), (21, 7, 1), (25, 10, 1), (26, 6, -1)]
  | 39 => [(1, 11, 1), (2, 11, -1), (3, 26, 1), (7, 23, -1), (8, 24, -1), (9, 25, -1), (18, 1, -1), (18, 2, 1), (19, 10, -1), (20, 4, 1), (21, 5, 1), (22, 6, 1)]
  | 40 => [(0, 26, -1), (2, 26, 1), (7, 15, 1), (8, 16, 1), (9, 17, 1), (10, 11, -1), (12, 4, -1), (13, 5, -1), (14, 6, -1), (18, 3, 1), (19, 0, 1), (19, 2, -1)]
  | 41 => [(0, 23, 1), (2, 23, -1), (3, 15, -1), (4, 11, 1), (8, 14, 1), (9, 13, -1), (12, 10, -1), (16, 6, 1), (17, 5, -1), (18, 7, 1), (20, 0, 1), (20, 2, -1)]
  | 42 => [(0, 24, 1), (2, 24, -1), (3, 16, -1), (5, 11, 1), (7, 14, -1), (9, 12, 1), (13, 10, -1), (15, 6, -1), (17, 4, 1), (18, 8, 1), (21, 0, 1), (21, 2, -1)]
  | 43 => [(0, 25, 1), (2, 25, -1), (3, 17, -1), (6, 11, 1), (7, 13, 1), (8, 12, -1), (14, 10, -1), (15, 5, 1), (16, 4, -1), (18, 9, 1), (22, 0, 1), (22, 2, -1)]
  | 44 => [(0, 20, 1), (2, 20, -1), (5, 17, -1), (6, 16, 1), (7, 18, 1), (10, 12, -1), (11, 4, 1), (13, 9, -1), (14, 8, 1), (15, 3, -1), (23, 0, 1), (23, 2, -1)]
  | 45 => [(0, 21, 1), (2, 21, -1), (4, 17, 1), (6, 15, -1), (8, 18, 1), (10, 13, -1), (11, 5, 1), (12, 9, 1), (14, 7, -1), (16, 3, -1), (24, 0, 1), (24, 2, -1)]
  | 46 => [(0, 22, 1), (2, 22, -1), (4, 16, -1), (5, 15, 1), (9, 18, 1), (10, 14, -1), (11, 6, 1), (12, 8, -1), (13, 7, 1), (17, 3, -1), (25, 0, 1), (25, 2, -1)]
  | 47 => [(0, 19, -1), (2, 19, 1), (3, 18, -1), (4, 12, 1), (5, 13, 1), (6, 14, 1), (11, 10, 1), (15, 7, -1), (16, 8, -1), (17, 9, -1), (26, 0, 1), (26, 2, -1)]
  | _ => []

private theorem four_smul_sub_slot (L D : Module.End ℝ (H3Zorn ℝ)) :
    (L + (2 * ((1 : ℤ) : ℝ)) • D) - (L + (2 * ((-1 : ℤ) : ℝ)) • D) = (4 : ℝ) • D := by
  simp only [Int.cast_one, Int.cast_neg]
  module

private theorem f4RootVec_coe_lt24 (r : Fin 48) (hr : r.val < 24) :
    (f4RootVec r : Module.End ℝ (H3Zorn ℝ)) =
      (e6RootVec ⟨r.val, by omega⟩ : Module.End ℝ (H3Zorn ℝ)) := by
  rcases r with ⟨k, hk⟩
  dsimp at hr
  interval_cases k <;>
    simp [f4RootVec, f4D4Pair, e6RootVec, e6RootSpec, rootOpFromSpec]

private theorem e6RootSpec_slot_even (k : Fin 24) :
    e6RootSpec ⟨24 + 2 * k.val, by omega⟩ =
      if hk8 : k.val < 8 then RootOpSpec.slot 0 ⟨k.val, hk8⟩ 1
      else if hk16 : k.val < 16 then RootOpSpec.slot 1 ⟨k.val - 8, by omega⟩ 1
      else RootOpSpec.slot 2 ⟨k.val - 16, by omega⟩ 1 := by
  fin_cases k <;> rfl

private theorem e6RootSpec_slot_odd (k : Fin 24) :
    e6RootSpec ⟨24 + 2 * k.val + 1, by omega⟩ =
      if hk8 : k.val < 8 then RootOpSpec.slot 0 ⟨k.val, hk8⟩ (-1)
      else if hk16 : k.val < 16 then RootOpSpec.slot 1 ⟨k.val - 8, by omega⟩ (-1)
      else RootOpSpec.slot 2 ⟨k.val - 16, by omega⟩ (-1) := by
  fin_cases k <;> rfl

private theorem f4RootVec_coe_ge24 (r : Fin 48) (hr : 24 ≤ r.val) :
    (f4RootVec r : Module.End ℝ (H3Zorn ℝ)) =
      (e6RootVec ⟨24 + 2 * (r.val - 24), by omega⟩ : Module.End ℝ (H3Zorn ℝ)) -
        (e6RootVec ⟨24 + 2 * (r.val - 24) + 1, by omega⟩ : Module.End ℝ (H3Zorn ℝ)) := by
  let k : Fin 24 := ⟨r.val - 24, by omega⟩
  have he : e6RootSpec ⟨24 + 2 * (r.val - 24), by omega⟩ = e6RootSpec ⟨24 + 2 * k.val, by omega⟩ :=
    rfl
  have ho : e6RootSpec ⟨24 + 2 * (r.val - 24) + 1, by omega⟩ =
      e6RootSpec ⟨24 + 2 * k.val + 1, by omega⟩ := rfl
  have h24 : ¬ r.val < 24 := Nat.not_lt.mpr hr
  change (f4RootVec r).1 =
    (rootOpFromSpec (e6RootSpec ⟨24 + 2 * (r.val - 24), by omega⟩)).1 -
      (rootOpFromSpec (e6RootSpec ⟨24 + 2 * (r.val - 24) + 1, by omega⟩)).1
  rw [he, ho, e6RootSpec_slot_even k, e6RootSpec_slot_odd k]
  simp only [f4RootVec, h24, ↓reduceDIte]
  by_cases hk8 : r.val - 24 < 8
  · have hk8' : k.val < 8 := hk8
    simp only [hk8, hk8', ↓reduceDIte]
    exact (four_smul_sub_slot _ _).symm
  · have hk8' : ¬ k.val < 8 := hk8
    simp only [hk8, hk8', ↓reduceDIte]
    by_cases hk16 : r.val - 24 < 16
    · have hk16' : k.val < 16 := hk16
      simp only [hk16, hk16', ↓reduceDIte]
      exact (four_smul_sub_slot _ _).symm
    · have hk16' : ¬ k.val < 16 := hk16
      simp only [hk16, hk16', ↓reduceDIte]
      exact (four_smul_sub_slot _ _).symm

private def f4RawSparse (r : Fin 48) : SparseMat27 :=
  if h : r.val < 24 then e6RootSparse ⟨r.val, by omega⟩
  else sparseSub (e6RootSparse ⟨24 + 2 * (r.val - 24), by omega⟩)
    (e6RootSparse ⟨24 + 2 * (r.val - 24) + 1, by omega⟩)

private theorem f4RootSparse_check (r : Fin 48) :
    sparseEq (f4RootSparse r) (f4RawSparse r) = true := by
  have h : (List.finRange 48).all (fun r => sparseEq (f4RootSparse r) (f4RawSparse r)) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at h
  exact h r

theorem h3zornToMatrix_f4RootVec (r : Fin 48) :
    h3zornToMatrix (f4RootVec r : Module.End ℝ (H3Zorn ℝ)) =
      (sparseToMat (f4RootSparse r)).map Int.cast := by
  have hsp := sparseToMat_eq_of_sparseEq (f4RootSparse_check r)
  rw [hsp]
  by_cases h24 : r.val < 24
  · rw [f4RootVec_coe_lt24 r h24]
    simp [f4RawSparse, h24, h3zornToMatrix_e6RootVec]
  · have hge : 24 ≤ r.val := by omega
    rw [f4RootVec_coe_ge24 r hge, map_sub, h3zornToMatrix_e6RootVec, h3zornToMatrix_e6RootVec]
    simp only [f4RawSparse, h24, ↓reduceDIte, sparseToMat_sub]
    ext a b; simp [Matrix.sub_apply]

def f4ESimpleIdx (i : Fin 4) : Fin 48 :=
  match i.val with
  | 0 => 12 | 1 => 16 | 2 => 30 | _ => 47

def f4ESimpleSign (i : Fin 4) : ℤ :=
  match i.val with
  | 0 => 1 | 1 => 1 | 2 => -1 | _ => -1

def f4FSimpleIdx (i : Fin 4) : Fin 48 :=
  match i.val with
  | 0 => 8 | 1 => 13 | 2 => 27 | _ => 40

def f4FSimpleSign (i : Fin 4) : ℤ :=
  match i.val with
  | 0 => 1 | 1 => 1 | 2 => -1 | _ => 1

def f4HighestRootIdx : Fin 48 := 3

/-- Simple raising Chevalley generators of `𝔣₄(4)`. -/
def f4SimpleE (i : Fin 4) : H3ZornF4Derivations :=
  (f4ESimpleSign i : ℝ) • f4RootVec (f4ESimpleIdx i)

/-- Simple lowering Chevalley generators of `𝔣₄(4)`. -/
def f4SimpleF (i : Fin 4) : H3ZornF4Derivations :=
  (f4FSimpleSign i : ℝ) • f4RootVec (f4FSimpleIdx i)

/-- Simple Cartan generators of `𝔣₄(4)`. -/
def f4SimpleH (i : Fin 4) : H3ZornF4Derivations :=
  ⁅f4SimpleE i, f4SimpleF i⁆

def f4SimpleESparse (i : Fin 4) : SparseMat27 :=
  sparseSmul (f4ESimpleSign i) (f4RootSparse (f4ESimpleIdx i))

def f4SimpleFSparse (i : Fin 4) : SparseMat27 :=
  sparseSmul (f4FSimpleSign i) (f4RootSparse (f4FSimpleIdx i))

def f4SimpleHSparse (i : Fin 4) : SparseMat27 :=
  sparseComm (f4SimpleESparse i) (f4SimpleFSparse i)

def f4CartanDiagSparse (i : Fin 4) : SparseMat27 :=
  match i.val with
  | 0 => [(4, 4, -1), (5, 5, 1), (7, 7, 1), (8, 8, -1), (12, 12, -1), (13, 13, 1), (15, 15, 1), (16, 16, -1), (20, 20, -1), (21, 21, 1), (23, 23, 1), (24, 24, -1)]
  | 1 => [(5, 5, -1), (6, 6, 1), (8, 8, 1), (9, 9, -1), (13, 13, -1), (14, 14, 1), (16, 16, 1), (17, 17, -1), (21, 21, -1), (22, 22, 1), (24, 24, 1), (25, 25, -1)]
  | 2 => [(6, 6, -2), (9, 9, 2), (11, 11, -1), (12, 12, 1), (13, 13, 1), (14, 14, -1), (15, 15, -1), (16, 16, -1), (17, 17, 1), (18, 18, 1), (19, 19, 1), (20, 20, 1), (21, 21, 1), (22, 22, -1), (23, 23, -1), (24, 24, -1), (25, 25, 1), (26, 26, -1)]
  | _ => [(3, 3, 1), (4, 4, 1), (5, 5, 1), (6, 6, 1), (7, 7, -1), (8, 8, -1), (9, 9, -1), (10, 10, -1), (11, 11, 1), (12, 12, -1), (13, 13, -1), (14, 14, -1), (15, 15, 1), (16, 16, 1), (17, 17, 1), (18, 18, -1), (19, 19, -2), (26, 26, 2)]

private theorem f4SimpleHSparse_eq_diag (i : Fin 4) :
    sparseEq (f4SimpleHSparse i) (f4CartanDiagSparse i) = true := by
  fin_cases i <;> decide

theorem h3zornToMatrix_f4SimpleE (i : Fin 4) :
    h3zornToMatrix (f4SimpleE i : Module.End ℝ (H3Zorn ℝ)) =
      (sparseToMat (f4SimpleESparse i)).map Int.cast := by
  change h3zornToMatrix ((f4ESimpleSign i : ℝ) • (f4RootVec (f4ESimpleIdx i) :
    Module.End ℝ (H3Zorn ℝ))) = _
  rw [map_smul, h3zornToMatrix_f4RootVec, f4SimpleESparse, sparseToMat_smul]
  ext r c; simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Int.cast_mul]

theorem h3zornToMatrix_f4SimpleF (i : Fin 4) :
    h3zornToMatrix (f4SimpleF i : Module.End ℝ (H3Zorn ℝ)) =
      (sparseToMat (f4SimpleFSparse i)).map Int.cast := by
  change h3zornToMatrix ((f4FSimpleSign i : ℝ) • (f4RootVec (f4FSimpleIdx i) :
    Module.End ℝ (H3Zorn ℝ))) = _
  rw [map_smul, h3zornToMatrix_f4RootVec, f4SimpleFSparse, sparseToMat_smul]
  ext r c; simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Int.cast_mul]

theorem h3zornToMatrix_f4_lie (X Y : H3ZornF4Derivations) :
    h3zornToMatrix (⁅X, Y⁆ : Module.End ℝ (H3Zorn ℝ)) =
      h3zornToMatrix X * h3zornToMatrix Y - h3zornToMatrix Y * h3zornToMatrix X := by
  change h3zornToMatrix ((X.1 : Module.End ℝ (H3Zorn ℝ)) * Y.1 - Y.1 * X.1) = _
  rw [map_sub, map_mul, map_mul]

theorem h3zornToMatrix_f4SimpleH (i : Fin 4) :
    h3zornToMatrix (f4SimpleH i : Module.End ℝ (H3Zorn ℝ)) =
      (sparseToMat (f4CartanDiagSparse i)).map Int.cast := by
  change h3zornToMatrix (⁅f4SimpleE i, f4SimpleF i⁆ : Module.End ℝ (H3Zorn ℝ)) = _
  rw [h3zornToMatrix_f4_lie, h3zornToMatrix_f4SimpleE, h3zornToMatrix_f4SimpleF,
    ← sparseToMat_eq_of_sparseEq (f4SimpleHSparse_eq_diag i), f4SimpleHSparse, sparseToMat_comm]
  ext r c; simp [Matrix.mul_apply]

/-- Folded Cartan generators equal the invariant combinations of `e6SimpleH`. -/
theorem f4SimpleH_coe_eq (i : Fin 4) :
    (f4SimpleH i : Module.End ℝ (H3Zorn ℝ)) = match i.val with
      | 0 => (e6SimpleH 1 : Module.End ℝ (H3Zorn ℝ))
      | 1 => (e6SimpleH 3 : Module.End ℝ (H3Zorn ℝ))
      | 2 => (e6SimpleH 2 : Module.End ℝ (H3Zorn ℝ)) + (e6SimpleH 4 : Module.End ℝ (H3Zorn ℝ))
      | _ => (e6SimpleH 0 : Module.End ℝ (H3Zorn ℝ)) + (e6SimpleH 5 : Module.End ℝ (H3Zorn ℝ)) := by
  have hchk : (List.finRange 4).all (fun i =>
      sparseEq (f4CartanDiagSparse i) (match i.val with
        | 0 => e6SimpleHSparse 1
        | 1 => e6SimpleHSparse 3
        | 2 => sparseAdd (e6SimpleHSparse 2) (e6SimpleHSparse 4)
        | _ => sparseAdd (e6SimpleHSparse 0) (e6SimpleHSparse 5))) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at hchk
  apply h3zornToMatrix.injective
  rw [h3zornToMatrix_f4SimpleH, sparseToMat_eq_of_sparseEq (hchk i)]
  fin_cases i <;>
    (simp [h3zornToMatrix_e6SimpleH, sparseToMat_add]; try (ext a b; simp [Matrix.add_apply]))

theorem f4SimpleH_comm (i j : Fin 4) : ⁅f4SimpleH i, f4SimpleH j⁆ = 0 := by
  have hchk : (List.finRange 4).all (fun i => (List.finRange 4).all (fun j =>
      sparseZeroCheck (sparseComm (f4CartanDiagSparse i) (f4CartanDiagSparse j)))) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at hchk
  apply Subtype.ext
  apply h3zornToMatrix.injective
  change h3zornToMatrix (⁅f4SimpleH i, f4SimpleH j⁆ : Module.End ℝ (H3Zorn ℝ)) =
    h3zornToMatrix (0 : Module.End ℝ (H3Zorn ℝ))
  rw [h3zornToMatrix_f4_lie, h3zornToMatrix_f4SimpleH, h3zornToMatrix_f4SimpleH, map_zero]
  have hcomm : (sparseToMat (f4CartanDiagSparse i)).map (Int.cast : ℤ → ℝ) *
        (sparseToMat (f4CartanDiagSparse j)).map Int.cast -
      (sparseToMat (f4CartanDiagSparse j)).map Int.cast *
        (sparseToMat (f4CartanDiagSparse i)).map Int.cast =
      (sparseToMat (sparseComm (f4CartanDiagSparse i) (f4CartanDiagSparse j))).map Int.cast := by
    rw [sparseToMat_comm]
    ext a b; simp [Matrix.mul_apply]
  rw [hcomm, sparseToMat_eq_zero_of_sparseZeroCheck (hchk i j)]
  ext a b; simp

/-- 4D split Cartan subalgebra of `H3ZornF4Derivations` (`𝔣₄(4)`). -/
def f4Cartan : LieSubalgebra ℝ H3ZornF4Derivations :=
  LieSubalgebra.lieSpan ℝ H3ZornF4Derivations (Set.range f4SimpleH)

private def f4CartanSpanSubalgebra : LieSubalgebra ℝ H3ZornF4Derivations where
  __ := Submodule.span ℝ (Set.range f4SimpleH)
  lie_mem' {x y} hx hy := by
    have hcomm_left : ∀ i (z : H3ZornF4Derivations),
        z ∈ Submodule.span ℝ (Set.range f4SimpleH) → ⁅f4SimpleH i, z⁆ = 0 := by
      intro i z hz
      induction hz using Submodule.span_induction with
      | zero => simp
      | add a b _ _ iha ihb => rw [lie_add, iha, ihb, add_zero]
      | smul r a _ iha => rw [lie_smul, iha, smul_zero]
      | mem _ h => rcases h with ⟨j, rfl⟩; exact f4SimpleH_comm i j
    have hcomm : ⁅x, y⁆ = 0 := by
      induction hx using Submodule.span_induction with
      | zero => simp
      | add a b _ _ iha ihb => rw [add_lie, iha, ihb, add_zero]
      | smul r a _ iha => rw [smul_lie, iha, smul_zero]
      | mem _ h => rcases h with ⟨i, rfl⟩; exact hcomm_left i y hy
    rw [hcomm]
    exact Submodule.zero_mem _

theorem f4Cartan_eq_span :
    f4Cartan.toSubmodule = Submodule.span ℝ (Set.range f4SimpleH) := by
  apply le_antisymm
  · change f4Cartan ≤ f4CartanSpanSubalgebra
    rw [f4Cartan, LieSubalgebra.lieSpan_le]
    rintro x ⟨i, rfl⟩
    exact Submodule.subset_span ⟨i, rfl⟩
  · rw [Submodule.span_le]
    rintro x ⟨i, rfl⟩
    exact LieSubalgebra.subset_lieSpan ⟨i, rfl⟩

@[simp] theorem mem_f4Cartan_iff (x : H3ZornF4Derivations) :
    x ∈ f4Cartan ↔ x ∈ Submodule.span ℝ (Set.range f4SimpleH) := by
  change x ∈ f4Cartan.toSubmodule ↔ _
  rw [f4Cartan_eq_span]

@[simp] theorem f4SimpleH_mem_f4Cartan (i : Fin 4) : f4SimpleH i ∈ f4Cartan :=
  (mem_f4Cartan_iff _).mpr (Submodule.subset_span ⟨i, rfl⟩)

instance : IsLieAbelian f4Cartan where
  trivial x y := by
    apply Subtype.ext
    rcases x with ⟨xv, hx⟩
    rcases y with ⟨yv, hy⟩
    change ⁅xv, yv⁆ = 0
    rw [mem_f4Cartan_iff] at hx hy
    induction hx using Submodule.span_induction with
    | zero => simp
    | add _ _ _ _ ih₁ ih₂ => rw [add_lie, ih₁, ih₂, add_zero]
    | smul c _ _ ih => rw [smul_lie, ih, smul_zero]
    | mem _ hx =>
      rcases hx with ⟨i, rfl⟩
      induction hy using Submodule.span_induction with
      | zero => simp
      | add _ _ _ _ ih₁ ih₂ => rw [lie_add, ih₁, ih₂, add_zero]
      | smul c _ _ ih => rw [lie_smul, ih, smul_zero]
      | mem _ hy =>
        rcases hy with ⟨j, rfl⟩
        exact f4SimpleH_comm i j

def f4RootCoord (r : Fin 48) : Fin 4 → ℤ :=
  match r.val with
  | 0 => ![0, 1, 2, 2]
  | 1 => ![1, 1, 2, 2]
  | 2 => ![1, 2, 2, 2]
  | 3 => ![2, 3, 4, 2]
  | 4 => ![1, 3, 4, 2]
  | 5 => ![1, 2, 4, 2]
  | 6 => ![-1, -2, -2, 0]
  | 7 => ![-1, -1, -2, 0]
  | 8 => ![-1, 0, 0, 0]
  | 9 => ![-1, -1, 0, 0]
  | 10 => ![-2, -3, -4, -2]
  | 11 => ![0, -1, -2, 0]
  | 12 => ![1, 0, 0, 0]
  | 13 => ![0, -1, 0, 0]
  | 14 => ![-1, -3, -4, -2]
  | 15 => ![1, 1, 0, 0]
  | 16 => ![0, 1, 0, 0]
  | 17 => ![-1, -2, -4, -2]
  | 18 => ![1, 2, 2, 0]
  | 19 => ![1, 1, 2, 0]
  | 20 => ![0, -1, -2, -2]
  | 21 => ![0, 1, 2, 0]
  | 22 => ![-1, -1, -2, -2]
  | 23 => ![-1, -2, -2, -2]
  | 24 => ![1, 2, 3, 2]
  | 25 => ![-1, -1, -1, 0]
  | 26 => ![0, -1, -1, 0]
  | 27 => ![0, 0, -1, 0]
  | 28 => ![1, 1, 1, 0]
  | 29 => ![0, 1, 1, 0]
  | 30 => ![0, 0, 1, 0]
  | 31 => ![-1, -2, -3, -2]
  | 32 => ![-1, -2, -3, -1]
  | 33 => ![-1, -1, -1, -1]
  | 34 => ![0, -1, -1, -1]
  | 35 => ![0, 0, -1, -1]
  | 36 => ![1, 1, 1, 1]
  | 37 => ![0, 1, 1, 1]
  | 38 => ![0, 0, 1, 1]
  | 39 => ![1, 2, 3, 1]
  | 40 => ![0, 0, 0, -1]
  | 41 => ![0, 1, 2, 1]
  | 42 => ![1, 1, 2, 1]
  | 43 => ![1, 2, 2, 1]
  | 44 => ![0, -1, -2, -1]
  | 45 => ![-1, -1, -2, -1]
  | 46 => ![-1, -2, -2, -1]
  | 47 => ![0, 0, 0, 1]
  | _ => ![0, 0, 0, 0]

def f4RootCertIdx (r : Fin 48) : Fin 48 :=
  match r.val with
  | 0 => 15 | 1 => 22 | 2 => 30 | 3 => 43 | 4 => 39 | 5 => 35 | 6 => 28 | 7 => 20
  | 8 => 4 | 9 => 12 | 10 => 46 | 11 => 14 | 12 => 0 | 13 => 6 | 14 => 42 | 15 => 5
  | 16 => 1 | 17 => 38 | 18 => 21 | 19 => 13 | 20 => 23 | 21 => 7 | 22 => 29 | 23 => 34
  | 24 => 44 | 25 => 26 | 26 => 18 | 27 => 9 | 28 => 16 | 29 => 8 | 30 => 2 | 31 => 47
  | 32 => 45 | 33 => 32 | 34 => 27 | 35 => 19 | 36 => 24 | 37 => 17 | 38 => 10 | 39 => 40
  | 40 => 11 | 41 => 25 | 42 => 31 | 43 => 36 | 44 => 33 | 45 => 37 | 46 => 41 | _ => 3

private theorem f4Certificate_check : f4Certificate.check = true := by decide
private theorem f4Certificate_roots_length : f4Certificate.roots.length = 48 := by decide

theorem f4RootCoord_eq_cert (r : Fin 48) :
    f4RootCoord r = f4Certificate.root (f4RootCertIdx r).val := by
  have h : (List.finRange 48).all (fun r =>
      List.ofFn (f4RootCoord r) == List.ofFn (f4Certificate.root (f4RootCertIdx r).val)) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at h
  exact List.ofFn_injective (h r)

theorem f4RootCoord_isRoot (r : Fin 48) : IsRoot .F4 (f4RootCoord r) := by
  rw [f4RootCoord_eq_cert r]
  exact RootCertificate.isRoot_root f4Certificate_check (f4RootCertIdx r).val
    (Nat.lt_of_lt_of_eq (f4RootCertIdx r).isLt f4Certificate_roots_length.symm)

theorem f4RootCoord_injective : Function.Injective f4RootCoord := by
  have hchk : (List.finRange 48).all (fun r₁ => (List.finRange 48).all (fun r₂ =>
      if r₁ = r₂ then true else !(List.ofFn (f4RootCoord r₁) == List.ofFn (f4RootCoord r₂)))) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at hchk
  intro r₁ r₂ heq
  by_contra hne
  have h12 := hchk r₁ r₂
  simp [hne, heq] at h12

/-- Canonical bijection between the 48 `F₄` root operators and `CFSGPort` `F₄` roots. -/
def f4RootEquiv : Fin 48 ≃ {v : Fin 4 → ℤ // IsRoot .F4 v} :=
  letI : Fintype {v : Fin 4 → ℤ // IsRoot .F4 v} :=
    (inferInstance : Fintype {v : Fin (Tag.rank .F4) → ℤ // IsRoot .F4 v})
  Equiv.ofBijective (fun r => ⟨f4RootCoord r, f4RootCoord_isRoot r⟩)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨fun _ _ h => f4RootCoord_injective (congrArg Subtype.val h),
       by rw [Fintype.card_fin]; exact (card_isRoot .F4).symm⟩)

def f4RootEigenvalue (i : Fin 4) (r : Fin 48) : ℤ :=
  ∑ j : Fin 4, Tag.cartan .F4 i j * f4RootCoord r j

private theorem f4RootBracket_check_0 (r : Fin 48) :
    sparseEq (sparseComm (f4CartanDiagSparse 0) (f4RootSparse r))
      (sparseSmul (f4RootEigenvalue 0 r) (f4RootSparse r)) = true := by
  have h : (List.finRange 48).all (fun r =>
      sparseEq (sparseComm (f4CartanDiagSparse 0) (f4RootSparse r))
        (sparseSmul (f4RootEigenvalue 0 r) (f4RootSparse r))) = true := by decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at h
  exact h r

private theorem f4RootBracket_check_1 (r : Fin 48) :
    sparseEq (sparseComm (f4CartanDiagSparse 1) (f4RootSparse r))
      (sparseSmul (f4RootEigenvalue 1 r) (f4RootSparse r)) = true := by
  have h : (List.finRange 48).all (fun r =>
      sparseEq (sparseComm (f4CartanDiagSparse 1) (f4RootSparse r))
        (sparseSmul (f4RootEigenvalue 1 r) (f4RootSparse r))) = true := by decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at h
  exact h r

private theorem f4RootBracket_check_2 (r : Fin 48) :
    sparseEq (sparseComm (f4CartanDiagSparse 2) (f4RootSparse r))
      (sparseSmul (f4RootEigenvalue 2 r) (f4RootSparse r)) = true := by
  have h : (List.finRange 48).all (fun r =>
      sparseEq (sparseComm (f4CartanDiagSparse 2) (f4RootSparse r))
        (sparseSmul (f4RootEigenvalue 2 r) (f4RootSparse r))) = true := by decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at h
  exact h r

private theorem f4RootBracket_check_3 (r : Fin 48) :
    sparseEq (sparseComm (f4CartanDiagSparse 3) (f4RootSparse r))
      (sparseSmul (f4RootEigenvalue 3 r) (f4RootSparse r)) = true := by
  have h : (List.finRange 48).all (fun r =>
      sparseEq (sparseComm (f4CartanDiagSparse 3) (f4RootSparse r))
        (sparseSmul (f4RootEigenvalue 3 r) (f4RootSparse r))) = true := by decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at h
  exact h r

theorem f4RootVec_bracket_H (i : Fin 4) (r : Fin 48) :
    ⁅f4SimpleH i, f4RootVec r⁆ = (f4RootEigenvalue i r : ℝ) • f4RootVec r := by
  have hchk : sparseEq (sparseComm (f4CartanDiagSparse i) (f4RootSparse r))
      (sparseSmul (f4RootEigenvalue i r) (f4RootSparse r)) = true := by
    fin_cases i
    · exact f4RootBracket_check_0 r
    · exact f4RootBracket_check_1 r
    · exact f4RootBracket_check_2 r
    · exact f4RootBracket_check_3 r
  apply Subtype.ext
  apply h3zornToMatrix.injective
  change h3zornToMatrix (⁅f4SimpleH i, f4RootVec r⁆ : Module.End ℝ (H3Zorn ℝ)) = _
  rw [h3zornToMatrix_f4_lie, h3zornToMatrix_f4SimpleH, h3zornToMatrix_f4RootVec]
  have hcomm : (sparseToMat (f4CartanDiagSparse i)).map (Int.cast : ℤ → ℝ) *
        (sparseToMat (f4RootSparse r)).map Int.cast -
      (sparseToMat (f4RootSparse r)).map Int.cast *
        (sparseToMat (f4CartanDiagSparse i)).map Int.cast =
      (sparseToMat (sparseComm (f4CartanDiagSparse i) (f4RootSparse r))).map Int.cast := by
    rw [sparseToMat_comm]
    ext a b; simp [Matrix.mul_apply]
  rw [hcomm, SetLike.val_smul, map_smul, h3zornToMatrix_f4RootVec,
    sparseToMat_eq_of_sparseEq hchk, sparseToMat_smul]
  ext a b; simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Int.cast_mul]

theorem f4Simple_bracket_EF_same (i : Fin 4) : ⁅f4SimpleE i, f4SimpleF i⁆ = f4SimpleH i := rfl

theorem f4Simple_bracket_HE (i j : Fin 4) :
    ⁅f4SimpleH i, f4SimpleE j⁆ = ((Tag.cartan .F4 i j : ℤ) : ℝ) • f4SimpleE j := by
  have hwt : f4RootEigenvalue i (f4ESimpleIdx j) = Tag.cartan .F4 i j := by
    have hchk : (List.finRange 4).all (fun i => (List.finRange 4).all (fun j =>
        f4RootEigenvalue i (f4ESimpleIdx j) == Tag.cartan .F4 i j)) = true := by
      decide
    simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at hchk
    exact hchk i j
  change ⁅f4SimpleH i, (f4ESimpleSign j : ℝ) • f4RootVec (f4ESimpleIdx j)⁆ = _
  rw [lie_smul, f4RootVec_bracket_H i (f4ESimpleIdx j), hwt]
  simp only [f4SimpleE, smul_smul, mul_comm]

theorem f4Simple_bracket_HF (i j : Fin 4) :
    ⁅f4SimpleH i, f4SimpleF j⁆ = (-(Tag.cartan .F4 i j : ℤ) : ℝ) • f4SimpleF j := by
  have hwt : f4RootEigenvalue i (f4FSimpleIdx j) = -Tag.cartan .F4 i j := by
    have hchk : (List.finRange 4).all (fun i => (List.finRange 4).all (fun j =>
        f4RootEigenvalue i (f4FSimpleIdx j) == -Tag.cartan .F4 i j)) = true := by
      decide
    simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at hchk
    exact hchk i j
  change ⁅f4SimpleH i, (f4FSimpleSign j : ℝ) • f4RootVec (f4FSimpleIdx j)⁆ = _
  rw [lie_smul, f4RootVec_bracket_H i (f4FSimpleIdx j), hwt]
  simp only [f4SimpleF, Int.cast_neg, smul_smul, mul_comm]

theorem f4RootEigenvalue_ne_zero (r : Fin 48) : ∃ i : Fin 4, f4RootEigenvalue i r ≠ 0 := by
  have h : (List.finRange 48).all (fun r =>
      (List.finRange 4).any (fun i => f4RootEigenvalue i r != 0)) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, List.any_eq_true, bne_iff_ne,
    ne_eq] at h
  obtain ⟨i, _, hi⟩ := h r
  exact ⟨i, hi⟩

theorem f4RootEigenvalue_eq_imp {r₁ r₂ : Fin 48}
    (h : ∀ i : Fin 4, f4RootEigenvalue i r₁ = f4RootEigenvalue i r₂) : r₁ = r₂ := by
  have hchk : (List.finRange 48).all (fun r₁ => (List.finRange 48).all (fun r₂ =>
      if r₁ = r₂ then true else
        (List.finRange 4).any (fun i => f4RootEigenvalue i r₁ != f4RootEigenvalue i r₂))) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at hchk
  by_contra hne
  have h12 := hchk r₁ r₂
  simp only [hne, ↓reduceIte, List.any_eq_true, List.mem_finRange, true_and, bne_iff_ne,
    ne_eq] at h12
  obtain ⟨i, hi⟩ := h12
  exact hi (h i)

theorem f4RootVec_ne_zero (r : Fin 48) : f4RootVec r ≠ 0 := by
  have hnz : (List.finRange 48).all (fun r => !sparseZeroCheck (f4RootSparse r)) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, Bool.not_eq_true'] at hnz
  intro h0
  have hm := congrArg (fun x : H3ZornF4Derivations =>
    h3zornToMatrix (x.1 : Module.End ℝ (H3Zorn ℝ))) h0
  rw [h3zornToMatrix_f4RootVec, ZeroMemClass.coe_zero, map_zero] at hm
  have hzm : sparseToMat (f4RootSparse r) = 0 := by
    ext a b
    have := congrFun (congrFun hm a) b
    simpa [Matrix.map_apply] using this
  have hzc : sparseZeroCheck (f4RootSparse r) = true := by
    simp only [sparseZeroCheck, List.all_eq_true, beq_iff_eq]
    intro p _
    exact congrFun (congrFun hzm p.1) p.2.1
  rw [hnz r] at hzc
  cases hzc

theorem f4SimpleH_linearIndependent : LinearIndependent ℝ f4SimpleH := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hc_end : (∑ i : Fin 4, c i • (f4SimpleH i : Module.End ℝ (H3Zorn ℝ))) = 0 := by
    have h0 := congrArg (Subtype.val : H3ZornF4Derivations → Module.End ℝ (H3Zorn ℝ)) hc
    simpa [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul] using h0
  have hsum_e6 : c 3 • e6SimpleH 0 + c 0 • e6SimpleH 1 + c 2 • e6SimpleH 2 +
      c 1 • e6SimpleH 3 + c 2 • e6SimpleH 4 + c 3 • e6SimpleH 5 = 0 := by
    apply Subtype.ext
    rw [Fin.sum_univ_four] at hc_end
    simp only [f4SimpleH_coe_eq, smul_add] at hc_end
    simpa [add_assoc, add_comm, add_left_comm] using hc_end
  let d : Fin 6 → ℝ := fun k => match k.val with
    | 0 => c 3 | 1 => c 0 | 2 => c 2 | 3 => c 1 | 4 => c 2 | _ => c 3
  have hd : ∑ k : Fin 6, d k • e6SimpleH k = 0 := by
    rw [Fin.sum_univ_six]
    simpa [d] using hsum_e6
  have h0 := Fintype.linearIndependent_iff.mp e6SimpleH_linearIndependent d hd
  intro i
  fin_cases i
  · exact h0 1
  · exact h0 3
  · exact h0 2
  · exact h0 0

theorem finrank_f4Cartan : Module.finrank ℝ f4Cartan = 4 := by
  have hli : LinearIndependent ℝ (fun i : Fin 4 =>
      (⟨f4SimpleH i, f4SimpleH_mem_f4Cartan i⟩ : f4Cartan)) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hc' : ∑ i : Fin 4, c i • f4SimpleH i = 0 := congrArg Subtype.val hc
    exact Fintype.linearIndependent_iff.mp f4SimpleH_linearIndependent c hc'
  have hsp : Submodule.span ℝ (Set.range (fun i : Fin 4 =>
      (⟨f4SimpleH i, f4SimpleH_mem_f4Cartan i⟩ : f4Cartan))) = ⊤ := by
    rw [Submodule.eq_top_iff']
    rintro ⟨x, hx⟩
    have hx' : x ∈ Submodule.span ℝ (Set.range f4SimpleH) := (mem_f4Cartan_iff x).mp hx
    suffices hmem : ∀ y (hy : y ∈ Submodule.span ℝ (Set.range f4SimpleH)),
        (⟨y, (mem_f4Cartan_iff y).mpr hy⟩ : f4Cartan) ∈ Submodule.span ℝ
          (Set.range fun i : Fin 4 => (⟨f4SimpleH i, f4SimpleH_mem_f4Cartan i⟩ : f4Cartan)) from
      hmem x hx'
    intro y hy
    induction hy using Submodule.span_induction with
    | zero => exact Submodule.zero_mem _
    | add _ _ _ _ ih₁ ih₂ => exact Submodule.add_mem _ ih₁ ih₂
    | smul r _ _ ih => exact Submodule.smul_mem _ r ih
    | mem _ h =>
      rcases h with ⟨i, rfl⟩
      exact Submodule.subset_span ⟨i, rfl⟩
  have hfin := finrank_span_eq_card hli
  rw [hsp, finrank_top] at hfin
  simpa using hfin

private theorem f4_coe_add (x y : H3ZornF4Derivations) : (x + y).1 = x.1 + y.1 := rfl

/-- The 52-element Chevalley basis `(f4SimpleH ⊕ f4RootVec)` of `H3ZornF4Derivations`. -/
theorem f4Chevalley_linearIndependent :
    LinearIndependent ℝ (Sum.elim f4SimpleH f4RootVec) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hsum : (∑ i : Fin 4, g (Sum.inl i) • f4SimpleH i) +
      (∑ r : Fin 48, g (Sum.inr r) • f4RootVec r) = 0 := by
    apply Subtype.ext
    have hg' := congrArg (Subtype.val : H3ZornF4Derivations → Module.End ℝ (H3Zorn ℝ)) hg
    simp only [ZeroMemClass.coe_zero, AddSubmonoidClass.coe_finsetSum, SetLike.val_smul,
      f4_coe_add] at hg' ⊢
    rw [Fintype.sum_sum_type] at hg'
    simp only [Sum.elim_inl, Sum.elim_inr] at hg'
    exact hg'
  have hkill := cartan_weight_kill_mem_generic f4SimpleH f4RootVec f4RootEigenvalue
    f4SimpleH_comm f4RootVec_bracket_H f4RootEigenvalue_ne_zero f4RootEigenvalue_eq_imp
    ⊥ (fun i x hx => by
      rw [Submodule.mem_bot] at hx
      subst hx
      simp)
    Finset.univ (∑ i : Fin 4, g (Sum.inl i) • f4SimpleH i)
    (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
    (fun r => g (Sum.inr r))
    (by rw [hsum]; exact Submodule.zero_mem _)
  have ha0 : ∀ i : Fin 4, g (Sum.inl i) = 0 := by
    have h0 : ∑ j : Fin 4, g (Sum.inl j) • f4SimpleH j = 0 := (Submodule.mem_bot ℝ).mp hkill.1
    exact Fintype.linearIndependent_iff.mp f4SimpleH_linearIndependent (fun i => g (Sum.inl i)) h0
  have hb0 : ∀ r : Fin 48, g (Sum.inr r) = 0 := by
    intro r
    have h0 : g (Sum.inr r) • f4RootVec r = 0 :=
      (Submodule.mem_bot ℝ).mp (hkill.2 r (Finset.mem_univ r))
    exact (smul_eq_zero.mp h0).resolve_right (f4RootVec_ne_zero r)
  rintro (i | r)
  · exact ha0 i
  · exact hb0 r

def f4ChevalleyBasis : Module.Basis (Fin 4 ⊕ Fin 48) ℝ H3ZornF4Derivations :=
  basisOfLinearIndependentOfCardEqFinrank f4Chevalley_linearIndependent
    (by rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, finrank_H3ZornF4Derivations])

@[simp] theorem f4ChevalleyBasis_inl (i : Fin 4) :
    f4ChevalleyBasis (Sum.inl i) = f4SimpleH i := by
  simp [f4ChevalleyBasis]

@[simp] theorem f4ChevalleyBasis_inr (r : Fin 48) :
    f4ChevalleyBasis (Sum.inr r) = f4RootVec r := by
  simp [f4ChevalleyBasis]

/-- `f4Cartan` is a genuine 4D split Cartan subalgebra of `H3ZornF4Derivations`. -/
instance f4Cartan_isCartanSubalgebra : f4Cartan.IsCartanSubalgebra where
  nilpotent := inferInstance
  self_normalizing := by
    apply le_antisymm _ f4Cartan.le_normalizer
    intro x hx
    have hrep := f4ChevalleyBasis.sum_repr x
    rw [Fintype.sum_sum_type] at hrep
    simp only [f4ChevalleyBasis_inl, f4ChevalleyBasis_inr] at hrep
    have hhpart : (∑ i : Fin 4, (f4ChevalleyBasis.repr x) (Sum.inl i) • f4SimpleH i) ∈ f4Cartan :=
      Submodule.sum_mem _ fun i _ => f4Cartan.smul_mem _ (f4SimpleH_mem_f4Cartan i)
    have hb0 : ∀ r : Fin 48, (f4ChevalleyBasis.repr x) (Sum.inr r) = 0 := by
      intro r
      obtain ⟨i, hi⟩ := f4RootEigenvalue_ne_zero r
      have hnorm : ⁅f4SimpleH i, x⁆ ∈ f4Cartan := by
        have hxmem := (LieSubalgebra.mem_normalizer_iff f4Cartan x).mp hx (f4SimpleH i)
          (f4SimpleH_mem_f4Cartan i)
        have hneg := f4Cartan.neg_mem hxmem
        rw [← lie_skew, neg_neg] at hneg
        exact hneg
      have hKillH : ⁅f4SimpleH i, ∑ j : Fin 4, (f4ChevalleyBasis.repr x) (Sum.inl j) • f4SimpleH j⁆ = 0 := by
        have hc := (inferInstance : IsLieAbelian f4Cartan).trivial
          ⟨f4SimpleH i, f4SimpleH_mem_f4Cartan i⟩ ⟨_, hhpart⟩
        exact congrArg Subtype.val hc
      have hbr : ⁅f4SimpleH i, x⁆ =
          ∑ q : Fin 48, ((f4ChevalleyBasis.repr x) (Sum.inr q) * (f4RootEigenvalue i q : ℝ)) •
            f4RootVec q := by
        conv_lhs => rw [← hrep]
        rw [lie_add, hKillH, zero_add, lie_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [lie_smul, f4RootVec_bracket_H, smul_smul]
      have hmem : (-⁅f4SimpleH i, x⁆) +
          ∑ q : Fin 48, ((f4ChevalleyBasis.repr x) (Sum.inr q) * (f4RootEigenvalue i q : ℝ)) •
            f4RootVec q ∈ (⊥ : Submodule ℝ H3ZornF4Derivations) := by
        rw [← hbr, neg_add_cancel]
        exact Submodule.zero_mem _
      have hkill := cartan_weight_kill_mem_generic f4SimpleH f4RootVec f4RootEigenvalue
        f4SimpleH_comm f4RootVec_bracket_H f4RootEigenvalue_ne_zero f4RootEigenvalue_eq_imp
        ⊥ (fun k y hy => by
          rw [Submodule.mem_bot] at hy; subst hy; simp)
        Finset.univ (-⁅f4SimpleH i, x⁆) ((mem_f4Cartan_iff _).mp (f4Cartan.neg_mem hnorm))
        (fun q => (f4ChevalleyBasis.repr x) (Sum.inr q) * (f4RootEigenvalue i q : ℝ)) hmem
      have hr0 : ((f4ChevalleyBasis.repr x) (Sum.inr r) * (f4RootEigenvalue i r : ℝ)) •
          f4RootVec r = 0 :=
        (Submodule.mem_bot ℝ).mp (hkill.2 r (Finset.mem_univ r))
      have hmul0 := (smul_eq_zero.mp hr0).resolve_right (f4RootVec_ne_zero r)
      exact (mul_eq_zero.mp hmul0).resolve_right (Int.cast_ne_zero.mpr hi)
    have hs0 : (∑ r : Fin 48, (f4ChevalleyBasis.repr x) (Sum.inr r) • f4RootVec r) = 0 :=
      Finset.sum_eq_zero fun r _ => by rw [hb0 r, zero_smul]
    rw [← hrep, hs0, add_zero]
    exact hhpart

def f4RootHeight (r : Fin 48) : ℤ := ∑ i : Fin 4, f4RootCoord r i

theorem f4RootHeight_bounds (r : Fin 48) :
    f4RootHeight r ≠ 0 ∧ -11 ≤ f4RootHeight r ∧ f4RootHeight r ≤ 11 := by
  have h : (List.finRange 48).all (fun r =>
      (f4RootHeight r != 0) && decide (-11 ≤ f4RootHeight r) && decide (f4RootHeight r ≤ 11)) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true, bne_iff_ne,
    ne_eq, decide_eq_true_eq] at h
  exact ⟨(h r).1.1, (h r).1.2, (h r).2⟩

def f4PosRaiseStep (r : Fin 48) : Fin 4 × Fin 48 × ℤ :=
  match r.val with
  | 0 => (0, 1, -1) | 1 => (1, 2, -1) | 2 => (2, 24, -1) | 4 => (0, 3, 1)
  | 5 => (1, 4, 1) | 12 => (1, 15, -1) | 15 => (2, 28, 1) | 16 => (0, 15, 1)
  | 18 => (3, 43, -1) | 19 => (1, 18, 1) | 21 => (0, 19, 1) | 24 => (2, 5, -2)
  | 28 => (2, 19, -2) | 29 => (0, 28, 1) | 30 => (1, 29, 1) | 36 => (2, 42, 1)
  | 37 => (0, 36, 1) | 38 => (1, 37, 1) | 39 => (3, 24, -1) | 41 => (0, 42, -1)
  | 42 => (1, 43, -1) | 43 => (2, 39, -1) | 47 => (2, 38, 1) | _ => (0, 3, 1)

def f4NegRaiseStep (r : Fin 48) : Fin 4 × Fin 48 × ℤ :=
  match r.val with
  | 6 => (1, 7, -1) | 7 => (0, 11, -1) | 9 => (0, 13, -1) | 10 => (0, 14, -1)
  | 11 => (2, 26, -1) | 14 => (1, 17, -1) | 17 => (2, 31, 1) | 20 => (3, 44, -1)
  | 22 => (0, 20, 1) | 23 => (1, 22, 1) | 25 => (0, 26, -1) | 26 => (1, 27, -1)
  | 31 => (2, 23, 2) | 32 => (2, 46, -1) | 33 => (0, 34, -1) | 34 => (1, 35, -1)
  | 35 => (2, 40, 1) | 44 => (2, 34, 1) | 45 => (0, 44, 1) | 46 => (1, 45, 1)
  | _ => (0, 8, 1)

def f4PosLowerStep (r : Fin 48) : Option (Fin 4 × Fin 48 × ℤ) :=
  match r.val with
  | 0 => some (0, 1, -1) | 1 => some (1, 2, -1) | 2 => some (2, 24, -2)
  | 4 => some (0, 3, 1) | 5 => some (1, 4, 1) | 12 => some (1, 15, -1)
  | 15 => some (2, 28, 2) | 16 => some (0, 15, 1) | 18 => some (3, 43, -2)
  | 19 => some (1, 18, 1) | 21 => some (0, 19, 1) | 24 => some (2, 5, -1)
  | 28 => some (2, 19, -1) | 29 => some (0, 28, 1) | 30 => some (1, 29, 1)
  | 36 => some (2, 42, 1) | 37 => some (0, 36, 1) | 38 => some (1, 37, 1)
  | 39 => some (3, 24, -1) | 41 => some (0, 42, -1) | 42 => some (1, 43, -1)
  | 43 => some (2, 39, -1) | 47 => some (2, 38, 1) | _ => none

def f4NegLowerStep (r : Fin 48) : Option (Fin 4 × Fin 48 × ℤ) :=
  match r.val with
  | 6 => some (1, 7, -1) | 7 => some (0, 11, -1) | 9 => some (0, 13, -1)
  | 10 => some (0, 14, -1) | 11 => some (2, 26, -2) | 14 => some (1, 17, -1)
  | 17 => some (2, 31, 2) | 20 => some (3, 44, -2) | 22 => some (0, 20, 1)
  | 23 => some (1, 22, 1) | 25 => some (0, 26, -1) | 26 => some (1, 27, -1)
  | 31 => some (2, 23, 1) | 32 => some (2, 46, -1) | 33 => some (0, 34, -1)
  | 34 => some (1, 35, -1) | 35 => some (2, 40, 1) | 44 => some (2, 34, 1)
  | 45 => some (0, 44, 1) | 46 => some (1, 45, 1) | _ => none

private theorem f4PosRaiseStep_spec (r : Fin 48) (hpos : 0 < f4RootHeight r)
    (hne : r ≠ f4HighestRootIdx) :
    let st := f4PosRaiseStep r
    ⁅f4SimpleE st.1, f4RootVec r⁆ = (st.2.2 : ℝ) • f4RootVec st.2.1 ∧
      f4RootHeight r < f4RootHeight st.2.1 ∧ st.2.2 ≠ 0 := by
  have hchk : (List.finRange 48).all (fun r =>
      if decide (0 < f4RootHeight r) && (r != f4HighestRootIdx) then
        let st := f4PosRaiseStep r
        sparseEq (sparseComm (f4SimpleESparse st.1) (f4RootSparse r))
          (sparseSmul st.2.2 (f4RootSparse st.2.1)) &&
        decide (f4RootHeight r < f4RootHeight st.2.1) &&
        (st.2.2 != 0)
      else true) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at hchk
  have hr := hchk r
  have hcond : (decide (0 < f4RootHeight r) && (r != f4HighestRootIdx)) = true := by
    simp [hpos, hne]
  simp only [hcond, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hr
  refine ⟨?_, hr.1.2, hr.2⟩
  apply Subtype.ext
  apply h3zornToMatrix.injective
  change h3zornToMatrix (⁅f4SimpleE (f4PosRaiseStep r).1, f4RootVec r⁆ :
    Module.End ℝ (H3Zorn ℝ)) = _
  rw [h3zornToMatrix_f4_lie, h3zornToMatrix_f4SimpleE, h3zornToMatrix_f4RootVec,
    SetLike.val_smul, map_smul, h3zornToMatrix_f4RootVec]
  have hcomm : (sparseToMat (f4SimpleESparse (f4PosRaiseStep r).1)).map (Int.cast : ℤ → ℝ) *
        (sparseToMat (f4RootSparse r)).map Int.cast -
      (sparseToMat (f4RootSparse r)).map Int.cast *
        (sparseToMat (f4SimpleESparse (f4PosRaiseStep r).1)).map Int.cast =
      (sparseToMat (sparseComm (f4SimpleESparse (f4PosRaiseStep r).1) (f4RootSparse r))).map
        Int.cast := by
    rw [sparseToMat_comm]
    ext a b; simp [Matrix.mul_apply]
  rw [hcomm, sparseToMat_eq_of_sparseEq hr.1.1, sparseToMat_smul]
  ext a b; simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Int.cast_mul]

private theorem f4NegRaiseStep_spec (r : Fin 48) (hneg : f4RootHeight r < -1) :
    let st := f4NegRaiseStep r
    ⁅f4SimpleE st.1, f4RootVec r⁆ = (st.2.2 : ℝ) • f4RootVec st.2.1 ∧
      f4RootHeight r < f4RootHeight st.2.1 ∧ f4RootHeight st.2.1 < 0 ∧ st.2.2 ≠ 0 := by
  have hchk : (List.finRange 48).all (fun r =>
      if decide (f4RootHeight r < -1) then
        let st := f4NegRaiseStep r
        sparseEq (sparseComm (f4SimpleESparse st.1) (f4RootSparse r))
          (sparseSmul st.2.2 (f4RootSparse st.2.1)) &&
        decide (f4RootHeight r < f4RootHeight st.2.1) &&
        decide (f4RootHeight st.2.1 < 0) &&
        (st.2.2 != 0)
      else true) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at hchk
  have hr := hchk r
  have hcond : decide (f4RootHeight r < -1) = true := decide_eq_true hneg
  simp only [hcond, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hr
  refine ⟨?_, hr.1.1.2, hr.1.2, hr.2⟩
  apply Subtype.ext
  apply h3zornToMatrix.injective
  change h3zornToMatrix (⁅f4SimpleE (f4NegRaiseStep r).1, f4RootVec r⁆ :
    Module.End ℝ (H3Zorn ℝ)) = _
  rw [h3zornToMatrix_f4_lie, h3zornToMatrix_f4SimpleE, h3zornToMatrix_f4RootVec,
    SetLike.val_smul, map_smul, h3zornToMatrix_f4RootVec]
  have hcomm : (sparseToMat (f4SimpleESparse (f4NegRaiseStep r).1)).map (Int.cast : ℤ → ℝ) *
        (sparseToMat (f4RootSparse r)).map Int.cast -
      (sparseToMat (f4RootSparse r)).map Int.cast *
        (sparseToMat (f4SimpleESparse (f4NegRaiseStep r).1)).map Int.cast =
      (sparseToMat (sparseComm (f4SimpleESparse (f4NegRaiseStep r).1) (f4RootSparse r))).map
        Int.cast := by
    rw [sparseToMat_comm]
    ext a b; simp [Matrix.mul_apply]
  rw [hcomm, sparseToMat_eq_of_sparseEq hr.1.1.1, sparseToMat_smul]
  ext a b; simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Int.cast_mul]

private theorem f4PosLowerStep_spec (r : Fin 48) (hpos : 0 < f4RootHeight r) :
    (f4PosLowerStep r = none → r = f4HighestRootIdx) ∧
    (∀ st, f4PosLowerStep r = some st →
      ⁅f4SimpleF st.1, f4RootVec st.2.1⁆ = (st.2.2 : ℝ) • f4RootVec r ∧
      f4RootHeight r < f4RootHeight st.2.1 ∧ 0 < f4RootHeight st.2.1 ∧ st.2.2 ≠ 0) := by
  have hchk : (List.finRange 48).all (fun r =>
      if decide (0 < f4RootHeight r) then
        match f4PosLowerStep r with
        | none => r == f4HighestRootIdx
        | some st =>
          sparseEq (sparseComm (f4SimpleFSparse st.1) (f4RootSparse st.2.1))
            (sparseSmul st.2.2 (f4RootSparse r)) &&
          decide (f4RootHeight r < f4RootHeight st.2.1) &&
          decide (0 < f4RootHeight st.2.1) &&
          (st.2.2 != 0)
      else true) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at hchk
  have hr := hchk r
  have hcond : decide (0 < f4RootHeight r) = true := decide_eq_true hpos
  simp only [hcond, ↓reduceIte] at hr
  constructor
  · intro hnone
    rw [hnone] at hr
    exact beq_iff_eq.mp hr
  · intro st hsome
    rw [hsome] at hr
    simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hr
    refine ⟨?_, hr.1.1.2, hr.1.2, hr.2⟩
    apply Subtype.ext
    apply h3zornToMatrix.injective
    change h3zornToMatrix (⁅f4SimpleF st.1, f4RootVec st.2.1⁆ :
      Module.End ℝ (H3Zorn ℝ)) = _
    rw [h3zornToMatrix_f4_lie, h3zornToMatrix_f4SimpleF, h3zornToMatrix_f4RootVec,
      SetLike.val_smul, map_smul, h3zornToMatrix_f4RootVec]
    have hcomm : (sparseToMat (f4SimpleFSparse st.1)).map (Int.cast : ℤ → ℝ) *
          (sparseToMat (f4RootSparse st.2.1)).map Int.cast -
        (sparseToMat (f4RootSparse st.2.1)).map Int.cast *
          (sparseToMat (f4SimpleFSparse st.1)).map Int.cast =
        (sparseToMat (sparseComm (f4SimpleFSparse st.1) (f4RootSparse st.2.1))).map Int.cast := by
      rw [sparseToMat_comm]
      ext a b; simp [Matrix.mul_apply]
    rw [hcomm, sparseToMat_eq_of_sparseEq hr.1.1.1, sparseToMat_smul]
    ext a b; simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Int.cast_mul]

private theorem f4NegLowerStep_spec (r : Fin 48) (hneg : f4RootHeight r < 0) :
    (f4NegLowerStep r = none → ∃ i : Fin 4, r = f4FSimpleIdx i) ∧
    (∀ st, f4NegLowerStep r = some st →
      ⁅f4SimpleF st.1, f4RootVec st.2.1⁆ = (st.2.2 : ℝ) • f4RootVec r ∧
      f4RootHeight r < f4RootHeight st.2.1 ∧ f4RootHeight st.2.1 < 0 ∧ st.2.2 ≠ 0) := by
  have hchk : (List.finRange 48).all (fun r =>
      if decide (f4RootHeight r < 0) then
        match f4NegLowerStep r with
        | none => (List.finRange 4).any (fun i => r == f4FSimpleIdx i)
        | some st =>
          sparseEq (sparseComm (f4SimpleFSparse st.1) (f4RootSparse st.2.1))
            (sparseSmul st.2.2 (f4RootSparse r)) &&
          decide (f4RootHeight r < f4RootHeight st.2.1) &&
          decide (f4RootHeight st.2.1 < 0) &&
          (st.2.2 != 0)
      else true) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at hchk
  have hr := hchk r
  have hcond : decide (f4RootHeight r < 0) = true := decide_eq_true hneg
  simp only [hcond, ↓reduceIte] at hr
  constructor
  · intro hnone
    rw [hnone] at hr
    simp only [List.any_eq_true, List.mem_finRange, beq_iff_eq, true_and] at hr
    exact hr
  · intro st hsome
    rw [hsome] at hr
    simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hr
    refine ⟨?_, hr.1.1.2, hr.1.2, hr.2⟩
    apply Subtype.ext
    apply h3zornToMatrix.injective
    change h3zornToMatrix (⁅f4SimpleF st.1, f4RootVec st.2.1⁆ :
      Module.End ℝ (H3Zorn ℝ)) = _
    rw [h3zornToMatrix_f4_lie, h3zornToMatrix_f4SimpleF, h3zornToMatrix_f4RootVec,
      SetLike.val_smul, map_smul, h3zornToMatrix_f4RootVec]
    have hcomm : (sparseToMat (f4SimpleFSparse st.1)).map (Int.cast : ℤ → ℝ) *
          (sparseToMat (f4RootSparse st.2.1)).map Int.cast -
        (sparseToMat (f4RootSparse st.2.1)).map Int.cast *
          (sparseToMat (f4SimpleFSparse st.1)).map Int.cast =
        (sparseToMat (sparseComm (f4SimpleFSparse st.1) (f4RootSparse st.2.1))).map Int.cast := by
      rw [sparseToMat_comm]
      ext a b; simp [Matrix.mul_apply]
    rw [hcomm, sparseToMat_eq_of_sparseEq hr.1.1.1, sparseToMat_smul]
    ext a b; simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Int.cast_mul]

private theorem f4NegHeight_negOne_eq_fSimple (r : Fin 48) (h1 : f4RootHeight r = -1) :
    ∃ i : Fin 4, r = f4FSimpleIdx i := by
  have hchk : (List.finRange 48).all (fun r =>
      if f4RootHeight r == -1 then
        (List.finRange 4).any (fun i => r == f4FSimpleIdx i)
      else true) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at hchk
  have hr := hchk r
  have hcond : (f4RootHeight r == -1) = true := beq_iff_eq.mpr h1
  simp only [hcond, ↓reduceIte, List.any_eq_true, List.mem_finRange, beq_iff_eq, true_and] at hr
  exact hr

private def f4CartanInvT : Matrix (Fin 4) (Fin 4) ℤ :=
  !![2, 3, 4, 2; 3, 6, 8, 4; 2, 4, 6, 3; 1, 2, 3, 2]

private theorem f4CartanInvT_mul_transpose (i k : Fin 4) :
    ∑ j : Fin 4, f4CartanInvT i j * Tag.cartan .F4 k j = if i = k then 1 else 0 := by
  have h : (List.finRange 4).all (fun i => (List.finRange 4).all (fun k =>
      (∑ j : Fin 4, f4CartanInvT i j * Tag.cartan .F4 k j) == (if i = k then 1 else 0))) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at h
  exact h i k

/-- Bundled split Chevalley data for `H3ZornF4Derivations` (`𝔣₄(4)`). -/
def f4SplitChevalleyData : SplitChevalleyData ℝ H3ZornF4Derivations 4 48 where
  rk_pos := by decide
  H := f4SimpleH
  E := f4SimpleE
  F := f4SimpleF
  R := f4RootVec
  basis := f4ChevalleyBasis
  basis_inl := f4ChevalleyBasis_inl
  basis_inr := f4ChevalleyBasis_inr
  ev := f4RootEigenvalue
  C := Tag.cartan .F4
  C_inv := f4CartanInvT
  detC := 1
  detC_ne_zero := by decide
  C_inv_mul_transpose := f4CartanInvT_mul_transpose
  C_diag i := by fin_cases i <;> decide
  eIdx := f4ESimpleIdx
  fIdx := f4FSimpleIdx
  eSgn := f4ESimpleSign
  fSgn := f4FSimpleSign
  eSgn_ne_zero i := by fin_cases i <;> decide
  fSgn_ne_zero i := by fin_cases i <;> decide
  e_eq _ := rfl
  f_eq _ := rfl
  hiIdx := f4HighestRootIdx
  ht := f4RootHeight
  maxHt := 11
  ht_bounds := f4RootHeight_bounds
  ht_hi := by decide
  ht_eSimple i := by fin_cases i <;> decide
  ht_fSimple i := by fin_cases i <;> decide
  negHeight_negOne_eq_fSimple := f4NegHeight_negOne_eq_fSimple
  posRaise := f4PosRaiseStep
  negRaise := f4NegRaiseStep
  posLower := f4PosLowerStep
  negLower := f4NegLowerStep
  bracket_HH := f4SimpleH_comm
  bracket_HR := f4RootVec_bracket_H
  bracket_HE := f4Simple_bracket_HE
  bracket_HF_same i := by
    rw [f4Simple_bracket_HF]
    have hc : Tag.cartan .F4 i i = 2 := by fin_cases i <;> decide
    rw [hc]
    norm_num
  bracket_EF_same := f4Simple_bracket_EF_same
  ev_ne_zero := f4RootEigenvalue_ne_zero
  ev_inj := f4RootEigenvalue_eq_imp
  posRaise_spec := f4PosRaiseStep_spec
  negRaise_spec := f4NegRaiseStep_spec
  posLower_spec := f4PosLowerStep_spec
  negLower_spec := f4NegLowerStep_spec

/-- **Unconditional Simplicity of Split `𝔣₄(4)`**:
`H3ZornF4Derivations` is a simple 52-dimensional real Lie algebra. -/
instance h3ZornF4Derivations_isSimple : LieAlgebra.IsSimple ℝ H3ZornF4Derivations :=
  f4SplitChevalleyData.isSimple

instance h3ZornF4Derivations_isSemisimple : LieAlgebra.IsSemisimple ℝ H3ZornF4Derivations :=
  inferInstance

instance h3ZornF4Derivations_hasTrivialRadical :
    LieAlgebra.HasTrivialRadical ℝ H3ZornF4Derivations :=
  inferInstance

theorem center_h3ZornF4Derivations_eq_bot :
    LieAlgebra.center ℝ H3ZornF4Derivations = ⊥ :=
  le_antisymm (LieAlgebra.center_le_radical _ _ |>.trans (by simp)) bot_le

/-- **Unconditional Simplicity of Complex `F₄(ℂ)`**:
`ℂ ⊗[ℝ] H3ZornF4Derivations` is a simple 52-dimensional complex Lie algebra. -/
instance complexH3ZornF4Derivations_isSimple :
    LieAlgebra.IsSimple ℂ (ℂ ⊗[ℝ] H3ZornF4Derivations) :=
  (f4SplitChevalleyData.extendScalars ℂ).isSimple

/-- Explicit non-commutativity witness on `Matrix (Fin 27) (Fin 27) ℝ` from `F₄` generators. -/
theorem f4_matrix27_real_noncomm_witness :
    ∃ A B : Matrix (Fin 27) (Fin 27) ℝ, A * B ≠ B * A := by
  refine ⟨h3zornToMatrix (f4SimpleH 0).1, h3zornToMatrix (f4SimpleE 0).1, ?_⟩
  intro heq
  have hsub : h3zornToMatrix (⁅f4SimpleH 0, f4SimpleE 0⁆ : Module.End ℝ (H3Zorn ℝ)) = 0 := by
    rw [h3zornToMatrix_f4_lie, heq, sub_self]
  have h0 : (⁅f4SimpleH 0, f4SimpleE 0⁆ : H3ZornF4Derivations) = 0 :=
    Subtype.ext (h3zornToMatrix.injective (by simpa using hsub))
  rw [f4Simple_bracket_HE] at h0
  have hc : Tag.cartan .F4 (0 : Fin 4) (0 : Fin 4) = 2 := by decide
  change ((Tag.cartan .F4 (0 : Fin 4) (0 : Fin 4) : ℤ) : ℝ) •
    ((1 : ℤ) : ℝ) • f4RootVec (f4ESimpleIdx 0) = 0 at h0
  rw [hc] at h0
  norm_num at h0
  exact f4RootVec_ne_zero (f4ESimpleIdx 0) h0

end F4ChevalleyAndSimplicity

end InfoGeometry.Algebra
