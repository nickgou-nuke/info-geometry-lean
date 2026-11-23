/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# InfoGeometry.Arithmetic.AlpogeDeligneSignOnlyCore

Self-contained Lean 4 core formalizing the repaired algebraic, Fourier-bilinear, and
cohomological-sign mechanisms from L. Alpöge's sign-only proof of Deligne's Frobenius
eigenvalue bound (`hexagon:2611.00789v1`):

1. **Section 1 (Lemma 2 — Distinct Power-Sum Pole Bound & Tensor-Tower Amplification)**:
   - `range_geom_mul_one_sub`: finite geometric series identity over any `CommRing R`.
   - `distinct_power_sum_eigenvalue_bound`: direct complex-plane telescoping bound showing
     that distinct `μ j : ℂ` with nonzero weights `m j ≠ 0` and power-sum growth
     `‖∑ j ∈ S, m j * (μ j) ^ n‖ ≤ C * B ^ n` (`B ≥ 0`) must satisfy `‖μ i‖ ≤ B`.
   - `positive_multiplicity_power_sum_bound`: auto-grouped variant requiring only
     strictly positive real weights `0 < w i` without an explicit `Set.InjOn` hypothesis.
   - `tensor_tower_eigenvalue_bound`: amplifies weak tensor-power bounds
     `‖α‖ ^ k ≤ (1 + ε) ^ k * q ^ (k * a + c)` for arbitrarily large `k` and every `ε > 0`
     to `‖α‖ ≤ q ^ a` (`q > 1`).
2. **Section 2 (Lemma 3 — Finite-Field Plancherel & Chained Transfer-Matrix Bound)**:
   - `fintype_card_nsmul_eq_zero`, `nonneg_pow_eq_one`, `addChar_norm_and_conj`: proves
     `‖ψ x‖ = 1` and `starRingEnd ℂ (ψ x) = ψ (-x)` from finite-group torsion (`ψ 0 = 1`).
   - `addChar_bilinear_orthogonality` & `fourier_bilinear_plancherel`: exact Parseval identity
     for a nontrivial additive character `ψ : E → ℂ` and nondegenerate bilinear pairing `b`.
   - `pathTailVec` & `chained_bilinear_transfer_l2_and_sum_bound`: inductive `ℓ²` and
     Cauchy–Schwarz sum bound along a `k = r + 1` bilinear transfer chain.
3. **Section 3 (scalar identity with absolute degree shift `+2`)**:
   - `gysin_plus_two_same_sign_remainder`: handles arbitrary dimension `D = d₀ + 1 ≥ 1`
     (including `D = 1` and `Y = ∅`), showing that subtracting `M^k` from `Q * N(Y)` via the
     Gysin `+2` shift cancels higher degrees and aligns `TK` and `TX (d₀ + 1)` with the same
     sign `(-1 : ℂ) ^ d₀`. Its inputs are equations on scalar sequences, not constructed
     cohomology groups, Frobenius actions, or a Gysin morphism.
-/

noncomputable section
open scoped BigOperators

namespace InfoGeometry.Arithmetic.AlpogeDeligneSignOnlyCore

/-! ### Section 1: Lemma 2 — Distinct Power-Sum Pole Bound & Tensor-Tower Amplification -/

theorem range_geom_mul_one_sub {R : Type*} [CommRing R] (z : R) (N : ℕ) :
    (∑ n ∈ Finset.range N, z ^ n) * (1 - z) = 1 - z ^ N := by
  induction N with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, add_mul, ih]; ring

theorem pow_le_one_nat {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (N : ℕ) : a ^ N ≤ 1 := by
  induction N with
  | zero => norm_num
  | succ k ih =>
    rw [pow_succ]
    calc a ^ k * a ≤ 1 * 1 := mul_le_mul ih ha1 ha0 zero_le_one
      _ = 1 := one_mul 1

/-- Elementary telescoping proof of Lemma 2(a): if distinct `μ j : ℂ` have nonzero weights
`m j ≠ 0` (guaranteed whenever two Frobenius traces enter `R` with the same sign!) and
`‖∑ m j * (μ j)^n‖ ≤ C * B^n` for all `n ≥ 1`, then every `‖μ i‖ ≤ B`. -/
theorem distinct_power_sum_eigenvalue_bound {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (μ m : ι → ℂ) {C B : ℝ} (hB : 0 ≤ B)
    (hInj : Set.InjOn μ S) (hm : ∀ j ∈ S, m j ≠ 0)
    (hBound : ∀ n : ℕ, 1 ≤ n → ‖∑ j ∈ S, m j * (μ j) ^ n‖ ≤ C * B ^ n) :
    ∀ i ∈ S, ‖μ i‖ ≤ B := by
  intro i₀ hi₀
  by_contra hlt
  push Not at hlt
  obtain ⟨j₀, hj₀, hmax⟩ := S.exists_max_image (fun j => ‖μ j‖) ⟨i₀, hi₀⟩
  have hBM : B < ‖μ j₀‖ := lt_of_lt_of_le hlt (hmax i₀ hi₀)
  have hMpos : 0 < ‖μ j₀‖ := lt_of_le_of_lt hB hBM
  have hμ0 : μ j₀ ≠ 0 := norm_pos_iff.mp hMpos
  let z : ι → ℂ := fun j => μ j * (μ j₀)⁻¹
  let r : ℝ := B / ‖μ j₀‖
  let C' : ℝ := max C 0
  have hr0 : 0 ≤ r := div_nonneg hB hMpos.le
  have hr1 : r < 1 := (div_lt_one hMpos).mpr hBM
  have hstep : ∀ n : ℕ, ‖∑ j ∈ S, m j * z j ^ (n + 1)‖ ≤ C' * r ^ (n + 1) := by
    intro n
    have hpull : (∑ j ∈ S, m j * z j ^ (n + 1)) =
        (∑ j ∈ S, m j * μ j ^ (n + 1)) * ((μ j₀)⁻¹) ^ (n + 1) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      dsimp [z]; rw [mul_pow, mul_assoc]
    rw [hpull, norm_mul, norm_pow, norm_inv]
    have hb := hBound (n + 1) (Nat.succ_pos n)
    have hC' : C * B ^ (n + 1) ≤ C' * B ^ (n + 1) :=
      mul_le_mul_of_nonneg_right (le_max_left C 0) (pow_nonneg hB _)
    calc ‖∑ j ∈ S, m j * μ j ^ (n + 1)‖ * ‖μ j₀‖⁻¹ ^ (n + 1)
        ≤ (C' * B ^ (n + 1)) * ‖μ j₀‖⁻¹ ^ (n + 1) :=
          mul_le_mul_of_nonneg_right (hb.trans hC') (pow_nonneg (inv_nonneg.mpr hMpos.le) _)
      _ = C' * r ^ (n + 1) := by dsimp [r]; rw [div_eq_mul_inv, mul_pow, mul_assoc]
  have hgeom : ∀ N : ℕ, ∑ n ∈ Finset.range N, r ^ (n + 1) ≤ 1 / (1 - r) := by
    intro N
    have hle : ∑ n ∈ Finset.range N, r ^ (n + 1) ≤ ∑ n ∈ Finset.range N, r ^ n :=
      Finset.sum_le_sum fun n _ => by
        rw [pow_succ]; exact mul_le_of_le_one_right (pow_nonneg hr0 n) hr1.le
    have htel := range_geom_mul_one_sub r N
    have hsub : (∑ n ∈ Finset.range N, r ^ n) * (1 - r) ≤ 1 := by
      rw [htel]; linarith [pow_nonneg hr0 N]
    exact hle.trans ((le_div_iff₀ (by linarith)).mpr hsub)
  have hother : ∀ j ∈ S.erase j₀, ∀ N : ℕ,
      ‖∑ n ∈ Finset.range N, z j ^ (n + 1)‖ ≤ 2 / ‖1 - z j‖ := by
    intro j hj N
    have hj_mem : j ∈ S := Finset.mem_of_mem_erase hj
    have hj_ne : j ≠ j₀ := Finset.ne_of_mem_erase hj
    have hzj_norm : ‖z j‖ ≤ 1 := by
      dsimp [z]; rw [norm_mul, norm_inv]
      exact (div_le_one hMpos).mpr (hmax j hj_mem)
    have h1z : 1 - z j ≠ 0 := by
      intro h0
      have hz1 : z j = 1 := (sub_eq_zero.mp h0).symm
      dsimp [z] at hz1
      exact hInj.ne hj_mem hj₀ hj_ne ((mul_inv_eq_one₀ hμ0).mp hz1)
    have hfactor : ∑ n ∈ Finset.range N, z j ^ (n + 1) =
        z j * ∑ n ∈ Finset.range N, z j ^ n := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      ring
    have hid : (∑ n ∈ Finset.range N, z j ^ (n + 1)) * (1 - z j) = z j * (1 - z j ^ N) := by
      rw [hfactor, mul_assoc, range_geom_mul_one_sub]
    have hnorm_id : ‖∑ n ∈ Finset.range N, z j ^ (n + 1)‖ * ‖1 - z j‖ ≤ 2 := by
      rw [← norm_mul, hid, norm_mul]
      have hzn : ‖1 - z j ^ N‖ ≤ 2 := by
        calc ‖1 - z j ^ N‖ ≤ ‖(1 : ℂ)‖ + ‖z j ^ N‖ := norm_sub_le _ _
          _ = 1 + ‖z j‖ ^ N := by simp [norm_pow]
          _ ≤ 1 + 1 := by linarith [pow_le_one_nat (norm_nonneg _) hzj_norm N]
          _ = 2 := by norm_num
      calc ‖z j‖ * ‖1 - z j ^ N‖ ≤ 1 * 2 :=
            mul_le_mul hzj_norm hzn (norm_nonneg _) zero_le_one
        _ = 2 := one_mul 2
    exact (le_div_iff₀ (norm_pos_iff.mpr h1z)).mpr hnorm_id
  let K_const : ℝ := C' / (1 - r) + ∑ j ∈ S.erase j₀, ‖m j‖ * (2 / ‖1 - z j‖)
  have hm0_pos : 0 < ‖m j₀‖ := norm_pos_iff.mpr (hm j₀ hj₀)
  obtain ⟨N, hN⟩ := exists_nat_gt (K_const / ‖m j₀‖)
  have hN_main : (N : ℝ) * ‖m j₀‖ ≤ K_const := by
    let G : ℂ := ∑ n ∈ Finset.range N, ∑ j ∈ S, m j * z j ^ (n + 1)
    have hG_upper : ‖G‖ ≤ C' / (1 - r) := by
      calc ‖G‖ ≤ ∑ n ∈ Finset.range N, ‖∑ j ∈ S, m j * z j ^ (n + 1)‖ := norm_sum_le _ _
        _ ≤ ∑ n ∈ Finset.range N, C' * r ^ (n + 1) := Finset.sum_le_sum fun n _ => hstep n
        _ = C' * ∑ n ∈ Finset.range N, r ^ (n + 1) := (Finset.mul_sum _ _ _).symm
        _ ≤ C' * (1 / (1 - r)) := mul_le_mul_of_nonneg_left (hgeom N) (le_max_right C 0)
        _ = C' / (1 - r) := mul_one_div C' (1 - r)
    have hG_split : G = (N : ℂ) * m j₀ +
        ∑ j ∈ S.erase j₀, m j * ∑ n ∈ Finset.range N, z j ^ (n + 1) := by
      dsimp [G]
      rw [Finset.sum_comm, ← Finset.add_sum_erase S _ hj₀]
      congr 1
      · have hz0 : z j₀ = 1 := mul_inv_cancel₀ hμ0
        simp [hz0]
      · refine Finset.sum_congr rfl fun j _ => (Finset.mul_sum _ _ _).symm
    have htri : ‖(N : ℂ) * m j₀‖ ≤
        ‖G‖ + ‖∑ j ∈ S.erase j₀, m j * ∑ n ∈ Finset.range N, z j ^ (n + 1)‖ := by
      have heq : (N : ℂ) * m j₀ =
          G - ∑ j ∈ S.erase j₀, m j * ∑ n ∈ Finset.range N, z j ^ (n + 1) := by
        rw [hG_split]; ring
      rw [heq]; exact norm_sub_le _ _
    rw [norm_mul, Complex.norm_natCast] at htri
    have htail : ‖∑ j ∈ S.erase j₀, m j * ∑ n ∈ Finset.range N, z j ^ (n + 1)‖ ≤
        ∑ j ∈ S.erase j₀, ‖m j‖ * (2 / ‖1 - z j‖) := by
      calc ‖∑ j ∈ S.erase j₀, m j * ∑ n ∈ Finset.range N, z j ^ (n + 1)‖
          ≤ ∑ j ∈ S.erase j₀, ‖m j * ∑ n ∈ Finset.range N, z j ^ (n + 1)‖ := norm_sum_le _ _
        _ = ∑ j ∈ S.erase j₀, ‖m j‖ * ‖∑ n ∈ Finset.range N, z j ^ (n + 1)‖ := by
              refine Finset.sum_congr rfl fun j _ => norm_mul _ _
        _ ≤ ∑ j ∈ S.erase j₀, ‖m j‖ * (2 / ‖1 - z j‖) :=
              Finset.sum_le_sum fun j hj =>
                mul_le_mul_of_nonneg_left (hother j hj N) (norm_nonneg _)
    exact htri.trans (add_le_add hG_upper htail)
  have hlt_mul : K_const < (N : ℝ) * ‖m j₀‖ := (div_lt_iff₀ hm0_pos).mp hN
  linarith

/-- Auto-grouped Lemma 2(a): arbitrary eigenvalue collisions are allowed when
all weights are strictly positive. -/
theorem positive_multiplicity_power_sum_bound {ι : Type*}
    (I : Finset ι) (μ : ι → ℂ) (w : ι → ℝ) {C B : ℝ} (hB : 0 ≤ B)
    (hw : ∀ i ∈ I, 0 < w i)
    (hBound : ∀ n : ℕ, 1 ≤ n →
      ‖∑ i ∈ I, (w i : ℂ) * (μ i) ^ n‖ ≤ C * B ^ n) :
    ∀ i ∈ I, ‖μ i‖ ≤ B := by
  classical
  let S : Finset ℂ := I.image μ
  let m : ℂ → ℂ := fun z => ∑ i ∈ I.filter (fun i => μ i = z), (w i : ℂ)
  have hm : ∀ z ∈ S, m z ≠ 0 := by
    intro z hz
    obtain ⟨i₀, hi₀, rfl⟩ := Finset.mem_image.mp hz
    have hpos : 0 < (m (μ i₀)).re := by
      dsimp [m]
      rw [Complex.re_sum]
      simp only [Complex.ofReal_re]
      exact Finset.sum_pos (fun i hi => hw i (Finset.mem_of_mem_filter i hi))
        ⟨i₀, Finset.mem_filter.mpr ⟨hi₀, rfl⟩⟩
    intro h0
    rw [h0, Complex.zero_re] at hpos
    exact lt_irrefl 0 hpos
  have hregroup : ∀ n : ℕ,
      (∑ z ∈ S, m z * z ^ n) = ∑ i ∈ I, (w i : ℂ) * (μ i) ^ n := by
    intro n
    dsimp [m]
    simp_rw [Finset.sum_mul, Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.sum_eq_single (μ i)]
    · simp
    · intro z _ hz; simp [hz.symm]
    · intro hnot; exfalso; exact hnot (Finset.mem_image_of_mem μ hi)
  have hS := distinct_power_sum_eigenvalue_bound (C := C) S
    (fun z : ℂ => z) m hB
    (fun _ _ _ _ h => h) hm
    (fun n hn => by simpa [hregroup n] using hBound n hn)
  intro i hi
  exact hS (μ i) (Finset.mem_image_of_mem μ hi)

/-- Lemma 2(b) Tensor-Tower Root Amplification: if `‖α‖^k ≤ (1 + ε)^k * q^(k * a + c)`
for arbitrarily large `k` and every `ε > 0` (killing `k`-independent overhead `q^c`),
then `‖α‖ ≤ q ^ a`. -/
theorem tensor_tower_eigenvalue_bound {α : ℂ} {q a c : ℝ} (hq : 1 < q)
    (htower : ∀ ε > 0, ∀ K : ℕ, ∃ k ≥ K, 1 ≤ k ∧
      ‖α‖ ^ k ≤ (1 + ε) ^ k * q ^ ((k : ℝ) * a + c)) :
    ‖α‖ ≤ q ^ a := by
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  have hlogq : 0 < Real.log q := Real.log_pos hq
  by_contra hlt
  push Not at hlt
  have hαpos : 0 < ‖α‖ := lt_trans (Real.rpow_pos_of_pos hq0 a) hlt
  let δ : ℝ := Real.log ‖α‖ - a * Real.log q
  have hδ : 0 < δ := by
    dsimp [δ]
    have hlog := Real.log_lt_log (Real.rpow_pos_of_pos hq0 a) hlt
    rw [Real.log_rpow hq0] at hlog; linarith
  let ε : ℝ := Real.exp (δ / 3) - 1
  have hε : 0 < ε := sub_pos.mpr (Real.one_lt_exp_iff.mpr (by linarith))
  obtain ⟨K, hK⟩ := exists_nat_gt (3 * |c| * Real.log q / δ)
  obtain ⟨k, hkK, hk1, hbound⟩ := htower ε hε (max K 1)
  have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr (lt_of_lt_of_le zero_lt_one hk1)
  have hlog_ineq := Real.log_le_log (pow_pos hαpos k) hbound
  rw [Real.log_pow, Real.log_mul (ne_of_gt (pow_pos (by linarith) k))
      (ne_of_gt (Real.rpow_pos_of_pos hq0 _)),
    Real.log_pow, Real.log_rpow hq0] at hlog_ineq
  have h1e : Real.log (1 + ε) = δ / 3 := by
    dsimp [ε]; rw [add_sub_cancel, Real.log_exp]
  rw [h1e] at hlog_ineq
  have hdiv : Real.log ‖α‖ - a * Real.log q ≤ δ / 3 + c * Real.log q / (k : ℝ) := by
    have hmul : (k : ℝ) * (Real.log ‖α‖ - a * Real.log q) ≤
        (k : ℝ) * (δ / 3) + c * Real.log q := by linarith
    calc Real.log ‖α‖ - a * Real.log q
        = ((k : ℝ) * (Real.log ‖α‖ - a * Real.log q)) / (k : ℝ) :=
            (mul_div_cancel_left₀ _ (ne_of_gt hk_pos)).symm
      _ ≤ ((k : ℝ) * (δ / 3) + c * Real.log q) / (k : ℝ) :=
            div_le_div_of_nonneg_right hmul hk_pos.le
      _ = δ / 3 + c * Real.log q / (k : ℝ) := by
            rw [add_div, mul_div_cancel_left₀ _ (ne_of_gt hk_pos)]
  have hK_le : (K : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr ((le_max_left K 1).trans hkK)
  have hc_lt : c * Real.log q / (k : ℝ) < δ / 3 := by
    calc c * Real.log q / (k : ℝ) ≤ |c| * Real.log q / (k : ℝ) :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_abs_self c) hlogq.le) hk_pos.le
      _ < δ / 3 := by
          have hk_gt : 3 * |c| * Real.log q / δ < (k : ℝ) := lt_of_lt_of_le hK hK_le
          have hmul := (div_lt_iff₀ hδ).mp hk_gt
          exact (div_lt_iff₀ hk_pos).mpr (by linarith)
  change δ ≤ δ / 3 + c * Real.log q / (k : ℝ) at hdiv
  linarith

/-! ### Section 2: Lemma 3 — Finite-Field Plancherel & Chained Transfer-Matrix Bound -/

theorem fintype_card_nsmul_eq_zero {G : Type*} [AddCommGroup G] [Fintype G] (x : G) :
    Fintype.card G • x = 0 := by
  have h1 : ∑ y : G, (x + y) = ∑ y : G, y :=
    Fintype.sum_equiv (Equiv.addLeft x) (fun y => x + y) (fun y => y) (fun _ => rfl)
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ] at h1
  exact add_right_cancel (h1.trans (zero_add _).symm)

theorem nonneg_pow_eq_one {r : ℝ} (hr : 0 ≤ r) {n : ℕ} (hn : 0 < n) (h : r ^ n = 1) :
    r = 1 := by
  rcases lt_trichotomy r 1 with hlt | rfl | hgt
  · exfalso
    have hlt' : r ^ n < 1 := pow_lt_one₀ hr hlt (ne_of_gt hn)
    linarith [h, hlt']
  · rfl
  · exfalso
    have hgt' : 1 < r ^ n := one_lt_pow₀ hgt (ne_of_gt hn)
    linarith [h, hgt']

theorem addChar_norm_and_conj {E : Type*} [AddCommGroup E] [Fintype E]
    (ψ : E → ℂ) (hψ0 : ψ 0 = 1) (hψ_add : ∀ x y, ψ (x + y) = ψ x * ψ y) (x : E) :
    ‖ψ x‖ = 1 ∧ starRingEnd ℂ (ψ x) = ψ (-x) := by
  have hnsmul : ∀ k : ℕ, ψ (k • x) = (ψ x) ^ k := by
    intro k; induction k with
    | zero => simp [hψ0]
    | succ m ih => rw [succ_nsmul, hψ_add, ih]; ring
  have hpow1 : (ψ x) ^ Fintype.card E = 1 := by
    rw [← hnsmul, fintype_card_nsmul_eq_zero, hψ0]
  have hn_norm : ‖ψ x‖ ^ Fintype.card E = 1 := by
    rw [← norm_pow, hpow1, norm_one]
  have hnorm1 : ‖ψ x‖ = 1 :=
    nonneg_pow_eq_one (norm_nonneg _) Fintype.card_pos hn_norm
  refine ⟨hnorm1, ?_⟩
  have hconj : ψ x * starRingEnd ℂ (ψ x) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm1]; norm_num
  have hinv : ψ x * ψ (-x) = 1 := by rw [← hψ_add, add_neg_cancel, hψ0]
  exact mul_left_cancel₀ (norm_ne_zero_iff.mp (by rw [hnorm1]; exact one_ne_zero))
    (hconj.trans hinv.symm)

theorem addChar_bilinear_orthogonality {E A : Type*} [Field E] [Fintype E]
    [AddCommGroup A] [Module E A] [Fintype A] [DecidableEq A]
    (ψ : E → ℂ) (hψ0 : ψ 0 = 1) (hψ_add : ∀ x y, ψ (x + y) = ψ x * ψ y)
    (hψ_ne : ∃ u : E, ψ u ≠ 1)
    (b : A →ₗ[E] A →ₗ[E] E) (hb : ∀ y : A, (∀ x : A, b x y = 0) → y = 0)
    {h : E} (hh : h ≠ 0) (y y' : A) :
    (∑ x : A, ψ (h * b x (y - y'))) = if y = y' then (Fintype.card A : ℂ) else 0 := by
  split_ifs with hy
  · subst hy; simp [hψ0]
  · have hsub : y - y' ≠ 0 := sub_ne_zero.mpr hy
    have hex : ∃ x₁ : A, b x₁ (y - y') ≠ 0 := by
      by_contra hall; push Not at hall; exact hsub (hb (y - y') hall)
    obtain ⟨x₁, hx₁⟩ := hex
    obtain ⟨u, hu⟩ := hψ_ne
    let a₀ : A := (u / (h * b x₁ (y - y'))) • x₁
    have ha₀ : h * b a₀ (y - y') = u := by
      dsimp [a₀]; rw [LinearMap.map_smul₂, smul_eq_mul]
      field_simp [hh, hx₁]
    have hshift : (∑ x : A, ψ (h * b x (y - y'))) =
        ψ u * ∑ x : A, ψ (h * b x (y - y')) := by
      calc (∑ x : A, ψ (h * b x (y - y')))
          = ∑ x : A, ψ (h * b (a₀ + x) (y - y')) :=
              (Fintype.sum_equiv (Equiv.addLeft a₀) _ _ fun _ => rfl).symm
        _ = ∑ x : A, ψ u * ψ (h * b x (y - y')) := by
              refine Finset.sum_congr rfl fun x _ => ?_
              rw [LinearMap.map_add₂, mul_add, hψ_add, ha₀]
        _ = ψ u * ∑ x : A, ψ (h * b x (y - y')) := (Finset.mul_sum _ _ _).symm
    have hzero : (1 - ψ u) * ∑ x : A, ψ (h * b x (y - y')) = 0 := by
      rw [sub_mul, one_mul, ← hshift, sub_self]
    exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hu.symm)

/-- Finite-Field Bilinear Plancherel Identity: the unitary Fourier-bilinear bond operator
`(K f)(x) = ∑_y ψ(h b(x, y)) f(y)` satisfies `∑_x ‖K f x‖² = |A| * ∑_y ‖f y‖²`. -/
theorem fourier_bilinear_plancherel {E A : Type*} [Field E] [Fintype E]
    [AddCommGroup A] [Module E A] [Fintype A] [DecidableEq A]
    (ψ : E → ℂ) (hψ0 : ψ 0 = 1) (hψ_add : ∀ x y, ψ (x + y) = ψ x * ψ y)
    (hψ_ne : ∃ u : E, ψ u ≠ 1)
    (b : A →ₗ[E] A →ₗ[E] E) (hb : ∀ y : A, (∀ x : A, b x y = 0) → y = 0)
    {h : E} (hh : h ≠ 0) (f : A → ℂ) :
    (∑ x : A, ‖∑ y : A, ψ (h * b x y) * f y‖ ^ 2) =
      (Fintype.card A : ℝ) * ∑ y : A, ‖f y‖ ^ 2 := by
  have hC : (∑ x : A, (∑ y : A, ψ (h * b x y) * f y) *
      starRingEnd ℂ (∑ y' : A, ψ (h * b x y') * f y')) =
      (Fintype.card A : ℂ) * ∑ y : A, f y * starRingEnd ℂ (f y) := by
    simp_rw [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    have hswap : ∀ y : A,
        (∑ x : A, ∑ y' : A, ψ (h * b x y) * f y * ((starRingEnd ℂ) (ψ (h * b x y')) *
          (starRingEnd ℂ) (f y'))) =
        ∑ y' : A, f y * (starRingEnd ℂ) (f y') * ∑ x : A, ψ (h * b x (y - y')) := by
      intro y
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun y' _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      have hconj := (addChar_norm_and_conj ψ hψ0 hψ_add (h * b x y')).2
      have hdiff : h * b x (y - y') = h * b x y + -(h * b x y') := by
        rw [map_sub, mul_sub, sub_eq_add_neg]
      rw [hdiff, hψ_add, ← hconj]; ring
    simp_rw [hswap, addChar_bilinear_orthogonality ψ hψ0 hψ_add hψ_ne b hb hh]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp [mul_ite, mul_zero]; ring
  have hre := congrArg Complex.re hC
  have hnormSq : ∀ z : ℂ, (z * starRingEnd ℂ z).re = ‖z‖ ^ 2 := fun z => by
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  rw [Complex.re_sum, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
    zero_mul, sub_zero, Complex.re_sum] at hre
  simpa only [hnormSq] using hre

/-- Recursive 1D MPO / transfer-chain vector `v_r` on `r + 1` vertices (`k = r + 1`). -/
def pathTailVec {E A : Type*} [Field E] [AddCommGroup A] [Module E A] [Fintype A]
    (ψ : E → ℂ) (h : E) :
    (r : ℕ) → (Fin (r + 1) → A → ℂ) → (Fin r → A →ₗ[E] A →ₗ[E] E) → A → ℂ
  | 0, t, _, x => t 0 x
  | r + 1, t, b, x =>
      t 0 x * ∑ y : A, ψ (h * b 0 x y) *
        pathTailVec ψ h r (fun i => t i.succ) (fun i => b i.succ) y

/-- Lemma 3 Square-Root Transfer-Chain Bound: along a `k = r + 1` nearest-neighbor
bilinear chain, `∑_x ‖v_r(x)‖² ≤ T^(2r + 2) * |A|^(r + 1)`, so Cauchy–Schwarz gives
`‖ψ(c) ∑_x v_r(x)‖ ≤ T^(r + 1) * |A|^((r + 2) / 2)`. -/
theorem chained_bilinear_transfer_l2_and_sum_bound
    {E A : Type*} [Field E] [Fintype E]
    [AddCommGroup A] [Module E A] [Fintype A] [DecidableEq A]
    (ψ : E → ℂ) (hψ0 : ψ 0 = 1) (hψ_add : ∀ x y, ψ (x + y) = ψ x * ψ y)
    (hψ_ne : ∃ u : E, ψ u ≠ 1) {h : E} (hh : h ≠ 0) (c : E)
    (r : ℕ) (t : Fin (r + 1) → A → ℂ) (b : Fin r → A →ₗ[E] A →ₗ[E] E)
    (hb : ∀ i : Fin r, ∀ y : A, (∀ x : A, b i x y = 0) → y = 0)
    {T : ℝ} (ht : ∀ i x, ‖t i x‖ ≤ T) :
    (∑ x : A, ‖pathTailVec ψ h r t b x‖ ^ 2 ≤
      T ^ (2 * r + 2) * (Fintype.card A : ℝ) ^ (r + 1)) ∧
    ‖ψ c * ∑ x : A, pathTailVec ψ h r t b x‖ ^ 2 ≤
      T ^ (2 * r + 2) * (Fintype.card A : ℝ) ^ (r + 2) := by
  have hl2 : ∑ x : A, ‖pathTailVec ψ h r t b x‖ ^ 2 ≤
      T ^ (2 * r + 2) * (Fintype.card A : ℝ) ^ (r + 1) := by
    induction r with
    | zero =>
      dsimp [pathTailVec]
      calc ∑ x : A, ‖t 0 x‖ ^ 2
          ≤ ∑ _ : A, T ^ 2 := Finset.sum_le_sum fun x _ =>
              pow_le_pow_left₀ (norm_nonneg _) (ht 0 x) 2
        _ = (Fintype.card A : ℝ) * T ^ 2 := by simp [Finset.sum_const, nsmul_eq_mul]
        _ = T ^ 2 * (Fintype.card A : ℝ) ^ 1 := by ring
    | succ m ih =>
      dsimp [pathTailVec]
      have hpoint : ∀ x : A,
          ‖t 0 x * ∑ y : A, ψ (h * b 0 x y) *
            pathTailVec ψ h m (fun i => t i.succ) (fun i => b i.succ) y‖ ^ 2 ≤
          T ^ 2 * ‖∑ y : A, ψ (h * b 0 x y) *
            pathTailVec ψ h m (fun i => t i.succ) (fun i => b i.succ) y‖ ^ 2 := by
        intro x
        rw [norm_mul, mul_pow]
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (norm_nonneg _) (ht 0 x) 2) (sq_nonneg _)
      calc ∑ x : A, ‖t 0 x * ∑ y : A, ψ (h * b 0 x y) *
              pathTailVec ψ h m (fun i => t i.succ) (fun i => b i.succ) y‖ ^ 2
          ≤ T ^ 2 * ∑ x : A, ‖∑ y : A, ψ (h * b 0 x y) *
              pathTailVec ψ h m (fun i => t i.succ) (fun i => b i.succ) y‖ ^ 2 := by
              rw [Finset.mul_sum]; exact Finset.sum_le_sum fun x _ => hpoint x
        _ = T ^ 2 * ((Fintype.card A : ℝ) * ∑ y : A,
              ‖pathTailVec ψ h m (fun i => t i.succ) (fun i => b i.succ) y‖ ^ 2) := by
              rw [fourier_bilinear_plancherel ψ hψ0 hψ_add hψ_ne (b 0) (hb 0) hh]
        _ ≤ T ^ 2 * ((Fintype.card A : ℝ) *
              (T ^ (2 * m + 2) * (Fintype.card A : ℝ) ^ (m + 1))) := by
              refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
                (ih (fun i => t i.succ) (fun i => b i.succ) (fun i => hb i.succ)
                  (fun i x => ht i.succ x)) (Nat.cast_nonneg _)) (sq_nonneg _)
        _ = T ^ (2 * (m + 1) + 2) * (Fintype.card A : ℝ) ^ (m + 2) := by ring
  refine ⟨hl2, ?_⟩
  rw [norm_mul, (addChar_norm_and_conj ψ hψ0 hψ_add c).1, one_mul]
  calc ‖∑ x : A, pathTailVec ψ h r t b x‖ ^ 2
      ≤ (∑ x : A, 1 * ‖pathTailVec ψ h r t b x‖) ^ 2 := by
          have h1 : ‖∑ x : A, pathTailVec ψ h r t b x‖ ≤
              ∑ x : A, 1 * ‖pathTailVec ψ h r t b x‖ := by
            simpa using norm_sum_le (Finset.univ : Finset A) (pathTailVec ψ h r t b)
          exact pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ (∑ _ : A, (1 : ℝ) ^ 2) * ∑ x : A, ‖pathTailVec ψ h r t b x‖ ^ 2 :=
          Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
    _ = (Fintype.card A : ℝ) * ∑ x : A, ‖pathTailVec ψ h r t b x‖ ^ 2 := by simp
    _ ≤ (Fintype.card A : ℝ) * (T ^ (2 * r + 2) * (Fintype.card A : ℝ) ^ (r + 1)) :=
          mul_le_mul_of_nonneg_left hl2 (Nat.cast_nonneg _)
    _ = T ^ (2 * r + 2) * (Fintype.card A : ℝ) ^ (r + 2) := by ring

/-! ### Section 3: Proposition 4 — Gysin `+2` Shift & Same-Sign Remainder `R` -/

/-- Proposition 4 Sign-Alignment Identity (`D = d₀ + 1 ≥ 1`, handling `D = 1` and `Y = ∅`
without `ℕ`-subtraction bugs): under Gysin `+2` degree-shift isomorphisms `TY a = TX (a + 2)`
for `a > d₀` and surjection `TY d₀ = TK + TX (d₀ + 2)`, subtracting `M^k` from `Q N(Y)`
cancels all higher cohomology and aligns `TK` and `TX (d₀ + 1)` with the EXACT SAME SIGN. -/
theorem gysin_plus_two_same_sign_remainder (d₀ : ℕ) (TX TY : ℕ → ℂ) (TK : ℂ)
    (hX_low : ∀ b : ℕ, b < d₀ + 1 → TX b = 0)
    (hY_low : ∀ a : ℕ, a < d₀ → TY a = 0)
    (hSES : TY d₀ = TK + TX (d₀ + 2))
    (hIso : ∀ a : ℕ, d₀ < a → TY a = TX (a + 2)) :
    (∑ a ∈ Finset.range (2 * d₀ + 1), (-1 : ℂ) ^ a * TY a) -
      (∑ b ∈ Finset.range (2 * d₀ + 3), (-1 : ℂ) ^ b * TX b) =
    (-1 : ℂ) ^ d₀ * (TK + TX (d₀ + 1)) := by
  have hshift : (∑ b ∈ Finset.range (2 * d₀ + 3), (-1 : ℂ) ^ b * TX b) =
      TX 0 - TX 1 + ∑ a ∈ Finset.range (2 * d₀ + 1), (-1 : ℂ) ^ a * TX (a + 2) := by
    rw [show 2 * d₀ + 3 = (2 * d₀ + 1) + 1 + 1 by omega,
      Finset.sum_range_succ', Finset.sum_range_succ']
    have hp : ∀ a : ℕ, (-1 : ℂ) ^ (a + 1 + 1) = (-1 : ℂ) ^ a := fun a => by
      rw [pow_succ, pow_succ]; ring
    simp only [pow_zero, hp]; ring
  rw [hshift]
  have hdiff : (∑ a ∈ Finset.range (2 * d₀ + 1), (-1 : ℂ) ^ a * TY a) -
      (TX 0 - TX 1 + ∑ a ∈ Finset.range (2 * d₀ + 1), (-1 : ℂ) ^ a * TX (a + 2)) =
      -TX 0 + TX 1 +
        ∑ a ∈ Finset.range (2 * d₀ + 1), (-1 : ℂ) ^ a * (TY a - TX (a + 2)) := by
    have hmul :
        (∑ a ∈ Finset.range (2 * d₀ + 1), (-1 : ℂ) ^ a * TY a) -
          ∑ a ∈ Finset.range (2 * d₀ + 1), (-1 : ℂ) ^ a * TX (a + 2) =
        ∑ a ∈ Finset.range (2 * d₀ + 1), (-1 : ℂ) ^ a * (TY a - TX (a + 2)) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun a _ => (mul_sub _ _ _).symm
    linear_combination hmul
  rw [hdiff]
  rcases d₀ with _ | m
  · simp [hX_low 0 (by omega), hSES]; ring
  · rw [hX_low 0 (by omega), hX_low 1 (by omega)]
    have hterm : ∀ a ∈ Finset.range (2 * (m + 1) + 1),
        (-1 : ℂ) ^ a * (TY a - TX (a + 2)) =
          if a = m then (-1 : ℂ) ^ (m + 1) * TX (m + 2)
          else if a = m + 1 then (-1 : ℂ) ^ (m + 1) * TK else 0 := by
      intro a _
      rcases lt_trichotomy a m with hlt | rfl | hgt
      · have h1 : a ≠ m := ne_of_lt hlt
        have h2 : a ≠ m + 1 := by omega
        simp [h1, h2, hY_low a (by omega), hX_low (a + 2) (by omega)]
      · simp [hY_low a (by omega), pow_succ]
      · rcases eq_or_lt_of_le (Nat.succ_le_of_lt hgt) with rfl | hgt2
        · simp [hSES]
        · have h1 : a ≠ m := by omega
          have h2 : a ≠ m + 1 := ne_of_gt hgt2
          simp [h1, h2, hIso a hgt2]
    rw [Finset.sum_congr rfl hterm]
    have hm_in : m ∈ Finset.range (2 * (m + 1) + 1) := Finset.mem_range.mpr (by omega)
    have hm1_in : m + 1 ∈ (Finset.range (2 * (m + 1) + 1)).erase m :=
      Finset.mem_erase.mpr ⟨by omega, Finset.mem_range.mpr (by omega)⟩
    rw [← Finset.add_sum_erase _ _ hm_in, ← Finset.add_sum_erase _ _ hm1_in]
    have hrest : ∀ a ∈ ((Finset.range (2 * (m + 1) + 1)).erase m).erase (m + 1),
        (if a = m then (-1 : ℂ) ^ (m + 1) * TX (m + 2)
         else if a = m + 1 then (-1 : ℂ) ^ (m + 1) * TK else 0) = 0 := by
      intro a ha
      have ha1 : a ≠ m + 1 := (Finset.mem_erase.mp ha).1
      have ha0 : a ≠ m := (Finset.mem_erase.mp (Finset.mem_erase.mp ha).2).1
      simp [ha0, ha1]
    rw [Finset.sum_eq_zero hrest]
    simp; ring

end InfoGeometry.Arithmetic.AlpogeDeligneSignOnlyCore
