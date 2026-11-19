/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.OperatorAlgebra.PeirceBiSandwich.PinchedSuperExtension
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Clifford-8 BdG Horizon, TFD Unitary, GKSL Kraus Completeness & Cosmological EoS

Formalizes Passes 6–7 (`L₀ ≺ … ≺ L₉`, `N₀ ≺ … ≺ N₉`) and Cosmological Condensate
(`R₀ ≺ … ≺ R₉`) of the Epistemic Compilation (*Solve et Coagula*):
1. Bi-graded Day-convolution localization `BiDayRel`, `biDay_global_congruence`, and
   off-shell Cayley unitary inversion `global_biCayley_unitary_inversion` on all of `B`.
2. Endogenous Supercolor bridge `G₈ = P₀ D₈ A₈ D₈ P₀` and symplectic spin-singlet
   Andreev retro-reflection (`endogenous_supercolor_bridge_theorem`,
   `endogenous_clifford8_singlet_andreev_closure`).
3. Dual chiral `N = 2_L ⊕ 2_R = 4` supercharge closure (`dual_chiral_supercharge_closure`),
   boost anticommutation and TFD unitarity (`boost_anticomm_and_tfd_unitary`),
   all-orders trigonometric horizon leakage (`all_orders_trigonometric_horizon_leakage`),
   and four-channel spin-chiral GKSL Kraus completeness (`four_channel_spin_chiral_kraus_completeness`).
4. Pregeometric spacetime vanishing iff `V = 0` (`pregeometric_spacetime_vanishes_iff_V_zero`),
   Lorentz boost invariance forcing `w = -1` (`lorentz_boost_invariance_forces_dark_energy_eos`),
   sector-selective boost breaking & photon shielding (`sector_selective_boost_breaking_and_photon_shielding`), and
   Bogoliubov cold matter vs. Goldstone radiation EoS (`bogoliubov_cold_matter_vs_goldstone_radiation_eos`).
-/

namespace InfoGeometry.OperatorAlgebra.PeirceBiSandwich

/-! ### Part I: Bi-Graded Day Localization & Off-Shell Cayley Dressing (`L₀ ≺ … ≺ L₅`) -/

/-- Bi-graded Day-convolution equivalence relation on `ℕ × B × ℕ`, representing `s⁻ᵏ X s⁻ˡ`. -/
def BiDayRel {B : Type*} [Ring B] (s : B) (t1 t2 : ℕ × B × ℕ) : Prop :=
  ∃ m n : ℕ,
    s ^ m * (s ^ t2.1 * t1.2.1 * s ^ t2.2.2) * s ^ n =
    s ^ m * (s ^ t1.1 * t2.2.1 * s ^ t1.2.2) * s ^ n

theorem biDayRel_refl {B : Type*} [Ring B] (s : B) (t : ℕ × B × ℕ) : BiDayRel s t t :=
  ⟨0, 0, rfl⟩

theorem biDayRel_symm {B : Type*} [Ring B] (s : B) {t1 t2 : ℕ × B × ℕ}
    (h : BiDayRel s t1 t2) : BiDayRel s t2 t1 :=
  let ⟨m, n, hmn⟩ := h
  ⟨m, n, hmn.symm⟩

private lemma pow_left {B : Type*} [Ring B] (s X : B) (a b : ℕ) :
    s ^ a * (s ^ b * X) = s ^ (a + b) * X := by
  rw [← mul_assoc, ← pow_add]

/-- Universal transitivity of `BiDayRel` on `ℕ × B × ℕ` without commutativity assumptions. -/
theorem biDayRel_trans {B : Type*} [Ring B] (s : B) {t1 t2 t3 : ℕ × B × ℕ}
    (h12 : BiDayRel s t1 t2) (h23 : BiDayRel s t2 t3) : BiDayRel s t1 t3 := by
  obtain ⟨m1, n1, hm1⟩ := h12
  obtain ⟨m2, n2, hm2⟩ := h23
  refine ⟨m1 + m2 + t2.1, n1 + n2 + t2.2.2, ?_⟩
  have h1 : s ^ (m1 + t2.1) * t1.2.1 * s ^ (t2.2.2 + n1) =
      s ^ (m1 + t1.1) * t2.2.1 * s ^ (t1.2.2 + n1) := by
    simpa [pow_add, mul_assoc] using hm1
  have h2 : s ^ (m2 + t3.1) * t2.2.1 * s ^ (t3.2.2 + n2) =
      s ^ (m2 + t2.1) * t3.2.1 * s ^ (t2.2.2 + n2) := by
    simpa [pow_add, mul_assoc] using hm2
  have hL : s ^ (m1 + m2 + t2.1) * (s ^ t3.1 * t1.2.1 * s ^ t3.2.2) * s ^ (n1 + n2 + t2.2.2) =
      s ^ (m2 + t3.1) * (s ^ (m1 + t2.1) * t1.2.1 * s ^ (t2.2.2 + n1)) * s ^ (t3.2.2 + n2) := by
    simp only [mul_assoc, ← pow_add, pow_left]
    exact congrArg₂ (· * ·) (congrArg (s ^ ·) (by omega)) (congrArg (t1.2.1 * s ^ ·) (by omega))
  have hMid : s ^ (m2 + t3.1) * (s ^ (m1 + t1.1) * t2.2.1 * s ^ (t1.2.2 + n1)) * s ^ (t3.2.2 + n2) =
      s ^ (m1 + t1.1) * (s ^ (m2 + t3.1) * t2.2.1 * s ^ (t3.2.2 + n2)) * s ^ (t1.2.2 + n1) := by
    simp only [mul_assoc, ← pow_add, pow_left]
    exact congrArg₂ (· * ·) (congrArg (s ^ ·) (by omega)) (congrArg (t2.2.1 * s ^ ·) (by omega))
  have hR : s ^ (m1 + t1.1) * (s ^ (m2 + t2.1) * t3.2.1 * s ^ (t2.2.2 + n2)) * s ^ (t1.2.2 + n1) =
      s ^ (m1 + m2 + t2.1) * (s ^ t1.1 * t3.2.1 * s ^ t1.2.2) * s ^ (n1 + n2 + t2.2.2) := by
    simp only [mul_assoc, ← pow_add, pow_left]
    exact congrArg₂ (· * ·) (congrArg (s ^ ·) (by omega)) (congrArg (t3.2.1 * s ^ ·) (by omega))
  rw [hL, h1, hMid, h2, hR]

/-- Canonical `Setoid` instance on `ℕ × B × ℕ` induced by `BiDayRel`. -/
def biDaySetoid {B : Type*} [Ring B] (s : B) : Setoid (ℕ × B × ℕ) where
  r := BiDayRel s
  iseqv := ⟨biDayRel_refl s, biDayRel_symm s, biDayRel_trans s⟩

/-- Bi-graded addition on `ℕ × B × ℕ`. -/
def biDayAdd {B : Type*} [Ring B] (s : B) (t1 t2 : ℕ × B × ℕ) : ℕ × B × ℕ :=
  (t1.1 + t2.1, s ^ t2.1 * t1.2.1 * s ^ t2.2.2 + s ^ t1.1 * t2.2.1 * s ^ t1.2.2, t1.2.2 + t2.2.2)

/-- Index-swapping `★`-involution on `ℕ × B × ℕ`: `(s⁻ᵏ X s⁻ˡ)* = s⁻ˡ X* s⁻ᵏ`. -/
def biDayStar {B : Type*} [Ring B] [StarRing B] (t : ℕ × B × ℕ) : ℕ × B × ℕ :=
  (t.2.2, star t.2.1, t.1)

/-- Left action of `(p, U)` on `(k, X, l) ∈ ℕ × B × ℕ`. -/
def biDayLeftAct {B : Type*} [Ring B] (p : ℕ) (U : B) (t : ℕ × B × ℕ) : ℕ × B × ℕ :=
  (p + t.1, U * t.2.1, t.2.2)

/-- Right action of `(q, W)` on `(k, X, l) ∈ ℕ × B × ℕ`. -/
def biDayRightAct {B : Type*} [Ring B] (q : ℕ) (W : B) (t : ℕ × B × ℕ) : ℕ × B × ℕ :=
  (t.1, t.2.1 * W, t.2.2 + q)

lemma pow_comm_of_comm {B : Type*} [Ring B] {s U : B} (h : s * U = U * s) (k : ℕ) :
    s ^ k * U = U * s ^ k := by
  induction k with
  | zero => simp
  | succ n ih => rw [pow_succ', mul_assoc, ih, ← mul_assoc, h, mul_assoc, ← pow_succ']

private lemma pow_add_swap {B : Type*} [Ring B] (s : B) (a b c : ℕ) :
    s ^ a * s ^ (b + c) = s ^ b * s ^ (a + c) := by
  rw [← pow_add, ← pow_add]
  congr 1
  omega

/-- Global congruence of `biDayStar`, `biDayAdd`, and `C_B(s)`-bimodule actions on all of `B`. -/
theorem biDay_global_congruence {B : Type*} [Ring B] [StarRing B] {s : B} (hs_star : star s = s)
    {t1 t2 t3 : ℕ × B × ℕ} (h12 : BiDayRel s t1 t2)
    {U W : B} (hU : s * U = U * s) (hW : s * W = W * s) (p q : ℕ) :
    BiDayRel s (biDayStar t1) (biDayStar t2) ∧
    BiDayRel s (biDayAdd s t1 t3) (biDayAdd s t2 t3) ∧
    BiDayRel s (biDayLeftAct p U t1) (biDayLeftAct p U t2) ∧
    BiDayRel s (biDayRightAct q W t1) (biDayRightAct q W t2) := by
  obtain ⟨m, n, hmn⟩ := h12
  have h_pow_star : ∀ k : ℕ, star (s ^ k) = s ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k' ih =>
      calc star (s ^ (k' + 1)) = star (s ^ k' * s) := by rw [pow_succ]
        _ = star s * star (s ^ k') := star_mul _ _
        _ = s * s ^ k' := by rw [hs_star, ih]
        _ = s ^ (k' + 1) := (pow_succ' s k').symm
  refine ⟨⟨n, m, ?_⟩, ⟨m, n, ?_⟩, ⟨m, n, ?_⟩, ⟨m, n, ?_⟩⟩
  · dsimp [biDayStar]
    have hstar := congrArg star hmn
    simp only [star_mul, h_pow_star, ← mul_assoc] at hstar ⊢
    exact hstar
  · dsimp [biDayAdd]
    simp only [mul_add, add_mul]
    congr 1
    · have hL : s ^ m * (s ^ (t2.1 + t3.1) * (s ^ t3.1 * t1.2.1 * s ^ t3.2.2) * s ^ (t2.2.2 + t3.2.2)) * s ^ n =
          s ^ (t3.1 + t3.1) * (s ^ m * (s ^ t2.1 * t1.2.1 * s ^ t2.2.2) * s ^ n) *
          s ^ (t3.2.2 + t3.2.2) := by
        simp only [mul_assoc, ← pow_add, pow_left]
        congr 1
        · congr 1; omega
        · congr 1; congr 1; omega
      have hR : s ^ m * (s ^ (t1.1 + t3.1) * (s ^ t3.1 * t2.2.1 * s ^ t3.2.2) * s ^ (t1.2.2 + t3.2.2)) * s ^ n =
          s ^ (t3.1 + t3.1) * (s ^ m * (s ^ t1.1 * t2.2.1 * s ^ t1.2.2) * s ^ n) *
          s ^ (t3.2.2 + t3.2.2) := by
        simp only [mul_assoc, ← pow_add, pow_left]
        congr 1
        · congr 1; omega
        · congr 1; congr 1; omega
      rw [hL, hR, hmn]
    · simp only [mul_assoc, ← pow_add, pow_left]
      congr 1
      · congr 1; omega
      · congr 1; congr 1; omega
  · dsimp [biDayLeftAct]
    have hL : s ^ m * (s ^ (p + t2.1) * (U * t1.2.1) * s ^ t2.2.2) * s ^ n =
        s ^ p * U * (s ^ m * (s ^ t2.1 * t1.2.1 * s ^ t2.2.2) * s ^ n) := by
      calc
        _ = s ^ p * U * (s ^ (m + t2.1) * t1.2.1 * s ^ t2.2.2) * s ^ n := by
          calc
            _ = (s ^ m * s ^ (p + t2.1)) * (U * t1.2.1) * s ^ t2.2.2 * s ^ n := by
              noncomm_ring
            _ = (s ^ p * s ^ (m + t2.1)) * (U * t1.2.1) * s ^ t2.2.2 * s ^ n := by
              rw [pow_add_swap]
            _ = s ^ p * (s ^ (m + t2.1) * U) * t1.2.1 * s ^ t2.2.2 * s ^ n := by
              noncomm_ring
            _ = s ^ p * (U * s ^ (m + t2.1)) * t1.2.1 * s ^ t2.2.2 * s ^ n := by
              rw [pow_comm_of_comm hU]
            _ = _ := by noncomm_ring
        _ = s ^ p * U * (s ^ m * (s ^ t2.1 * t1.2.1 * s ^ t2.2.2) * s ^ n) := by
          calc
            _ = s ^ p * U * (s ^ (m + t2.1) * (t1.2.1 * s ^ t2.2.2)) * s ^ n := by
              noncomm_ring
            _ = _ := by
              rw [(pow_left s (t1.2.1 * s ^ t2.2.2) m t2.1).symm]
              noncomm_ring
    have hR : s ^ m * (s ^ (p + t1.1) * (U * t2.2.1) * s ^ t1.2.2) * s ^ n =
        s ^ p * U * (s ^ m * (s ^ t1.1 * t2.2.1 * s ^ t1.2.2) * s ^ n) := by
      calc
        _ = s ^ p * U * (s ^ (m + t1.1) * t2.2.1 * s ^ t1.2.2) * s ^ n := by
          calc
            _ = (s ^ m * s ^ (p + t1.1)) * (U * t2.2.1) * s ^ t1.2.2 * s ^ n := by
              noncomm_ring
            _ = (s ^ p * s ^ (m + t1.1)) * (U * t2.2.1) * s ^ t1.2.2 * s ^ n := by
              rw [pow_add_swap]
            _ = s ^ p * (s ^ (m + t1.1) * U) * t2.2.1 * s ^ t1.2.2 * s ^ n := by
              noncomm_ring
            _ = s ^ p * (U * s ^ (m + t1.1)) * t2.2.1 * s ^ t1.2.2 * s ^ n := by
              rw [pow_comm_of_comm hU]
            _ = _ := by noncomm_ring
        _ = s ^ p * U * (s ^ m * (s ^ t1.1 * t2.2.1 * s ^ t1.2.2) * s ^ n) := by
          calc
            _ = s ^ p * U * (s ^ (m + t1.1) * (t2.2.1 * s ^ t1.2.2)) * s ^ n := by
              noncomm_ring
            _ = _ := by
              rw [(pow_left s (t2.2.1 * s ^ t1.2.2) m t1.1).symm]
              noncomm_ring
    rw [hL, hR, hmn]
  · dsimp [biDayRightAct]
    have hL : s ^ m * (s ^ t2.1 * (t1.2.1 * W) * s ^ (t2.2.2 + q)) * s ^ n =
        (s ^ m * (s ^ t2.1 * t1.2.1 * s ^ t2.2.2) * s ^ n) * W * s ^ q := by
      calc s ^ m * (s ^ t2.1 * (t1.2.1 * W) * s ^ (t2.2.2 + q)) * s ^ n
          = (s ^ (m + t2.1) * t1.2.1) * (W * s ^ (t2.2.2 + n)) * s ^ q := by
            calc
              _ = s ^ m * s ^ t2.1 * t1.2.1 * W * (s ^ t2.2.2 * (s ^ q * s ^ n)) := by
                rw [pow_add]; noncomm_ring
              _ = s ^ m * s ^ t2.1 * t1.2.1 * W * (s ^ t2.2.2 * (s ^ n * s ^ q)) := by
                rw [← pow_add s q n, add_comm q n, pow_add s n q]
              _ = _ := by
                rw [pow_add, pow_add]; noncomm_ring
        _ = (s ^ (m + t2.1) * t1.2.1) * (s ^ (t2.2.2 + n) * W) * s ^ q := by
            rw [← pow_comm_of_comm hW]
        _ = (s ^ m * (s ^ t2.1 * t1.2.1 * s ^ t2.2.2) * s ^ n) * W * s ^ q := by
            simp only [mul_assoc, ← pow_add, pow_left]
    have hR : s ^ m * (s ^ t1.1 * (t2.2.1 * W) * s ^ (t1.2.2 + q)) * s ^ n =
        (s ^ m * (s ^ t1.1 * t2.2.1 * s ^ t1.2.2) * s ^ n) * W * s ^ q := by
      calc s ^ m * (s ^ t1.1 * (t2.2.1 * W) * s ^ (t1.2.2 + q)) * s ^ n
          = (s ^ (m + t1.1) * t2.2.1) * (W * s ^ (t1.2.2 + n)) * s ^ q := by
            calc
              _ = s ^ m * s ^ t1.1 * t2.2.1 * W * (s ^ t1.2.2 * (s ^ q * s ^ n)) := by
                rw [pow_add]; noncomm_ring
              _ = s ^ m * s ^ t1.1 * t2.2.1 * W * (s ^ t1.2.2 * (s ^ n * s ^ q)) := by
                rw [← pow_add s q n, add_comm q n, pow_add s n q]
              _ = _ := by
                rw [pow_add, pow_add]; noncomm_ring
        _ = (s ^ (m + t1.1) * t2.2.1) * (s ^ (t1.2.2 + n) * W) * s ^ q := by
            rw [← pow_comm_of_comm hW]
        _ = (s ^ m * (s ^ t1.1 * t2.2.1 * s ^ t1.2.2) * s ^ n) * W * s ^ q := by
            simp only [mul_assoc, ← pow_add, pow_left]
    rw [hL, hR, hmn]

/-- Two-sided off-shell Cayley conjugation `Ad_{u_{J,∞}}` on `ℕ × B × ℕ`. -/
def biCayleyConj {B : Type*} [Ring B] (P A C : B) (t : ℕ × B × ℕ) : ℕ × B × ℕ :=
  let V := casimirV P A C
  let J := jOp P A C
  (t.1 + 1, (1 - V + 2 * J) * t.2.1 * (1 - V - 2 * J), t.2.2 + 1)

/-- Inverse two-sided off-shell Cayley conjugation on `ℕ × B × ℕ`. -/
def biCayleyConjInv {B : Type*} [Ring B] (P A C : B) (t : ℕ × B × ℕ) : ℕ × B × ℕ :=
  let V := casimirV P A C
  let J := jOp P A C
  (t.1 + 1, (1 - V - 2 * J) * t.2.1 * (1 - V + 2 * J), t.2.2 + 1)

/-- Global off-shell unitary Cayley dressing on all of `B`: commutes with `biDayStar`
    and is strictly inverted by `biCayleyConjInv` in `BiDayRel (1 + V)`. -/
theorem global_biCayley_unitary_inversion {B : Type*} [Ring B] [StarRing B]
    {P A : B} (hP : delta P = 0) (hP_star : star P = P) (X : B) :
    let V := casimirV P A (star A)
    let s := 1 + V
    biDayStar (biCayleyConj P A (star A) (0, X, 0)) =
      biCayleyConj P A (star A) (biDayStar (0, X, 0)) ∧
    BiDayRel s (biCayleyConjInv P A (star A) (biCayleyConj P A (star A) (0, X, 0))) (0, X, 0) := by
  intro V s
  have hNp_star : star (Nplus P A) = Nminus P (star A) := by
    dsimp [Nplus, Nminus]; simp only [star_mul, star_sub, star_one, hP_star, mul_assoc]
  have hNm_star : star (Nminus P (star A)) = Nplus P A := by
    rw [← hNp_star, star_star]
  have hV_star : star V = V := by
    dsimp [V, casimirV, Qplus, Qminus]
    simp only [star_add, star_mul, hNp_star, hNm_star]
  have hJ_star : star (jOp P A (star A)) = -jOp P A (star A) := by
    dsimp [jOp]; simp only [star_sub, hNp_star, hNm_star]; noncomm_ring
  have hVJ : V * jOp P A (star A) = jOp P A (star A) * V := by
    dsimp [V, jOp]; rw [mul_sub, sub_mul, V_comm_Nplus hP, V_comm_Nminus hP]
  have hj2 : jOp P A (star A) * jOp P A (star A) = -V := by
    dsimp [jOp, V, casimirV, Qplus, Qminus]
    calc (Nplus P A - Nminus P (star A)) * (Nplus P A - Nminus P (star A))
        = Nplus P A * Nplus P A - (Nplus P A * Nminus P (star A) + Nminus P (star A) * Nplus P A) +
          Nminus P (star A) * Nminus P (star A) := by noncomm_ring
      _ = -(Nplus P A * Nminus P (star A) + Nminus P (star A) * Nplus P A) := by
          rw [Nplus_sq hP, Nminus_sq hP]; noncomm_ring
  have hpyth1 : (1 - V - 2 * jOp P A (star A)) * (1 - V + 2 * jOp P A (star A)) = s ^ 2 := by
    dsimp [s]
    calc (1 - V - 2 * jOp P A (star A)) * (1 - V + 2 * jOp P A (star A))
        = (1 - V) ^ 2 + 2 * (jOp P A (star A) * V - V * jOp P A (star A)) -
          4 * (jOp P A (star A) * jOp P A (star A)) := by noncomm_ring
      _ = (1 + V) ^ 2 := by rw [hVJ, hj2]; noncomm_ring
  refine ⟨?_, ⟨0, 0, ?_⟩⟩
  · dsimp [biDayStar, biCayleyConj]
    ext
    · rfl
    · change star ((1 - V + 2 * jOp P A (star A)) * X * (1 - V - 2 * jOp P A (star A))) =
        (1 - V + 2 * jOp P A (star A)) * star X * (1 - V - 2 * jOp P A (star A))
      simp only [star_mul, star_add, star_sub, star_one, star_ofNat, hV_star, hJ_star]
      noncomm_ring
    · rfl
  · dsimp [biCayleyConjInv, biCayleyConj]
    simp only [pow_zero, one_mul, mul_one]
    calc (1 - V - 2 * jOp P A (star A)) *
           ((1 - V + 2 * jOp P A (star A)) * X * (1 - V - 2 * jOp P A (star A))) *
           (1 - V + 2 * jOp P A (star A))
        = ((1 - V - 2 * jOp P A (star A)) * (1 - V + 2 * jOp P A (star A))) * X *
          ((1 - V - 2 * jOp P A (star A)) * (1 - V + 2 * jOp P A (star A))) := by noncomm_ring
      _ = s ^ 2 * X * s ^ 2 := by rw [hpyth1]

/-! ### Part II: Endogenous Clifford-8 Triad & Dual Chiral Closure (`L₆–L₉`, `N₂–N₇`) -/

/-- Real Clifford elliptic spin/helicity generator `J₈` (`J₈² = -1`, `J₈ᵀ = -J₈`). -/
def J8_spin_Z : Matrix (Fin 8) (Fin 8) ℤ :=
  Matrix.of fun i j =>
    if (i = 0 ∧ j = 1) ∨ (i = 2 ∧ j = 3) ∨ (i = 4 ∧ j = 5) ∨ (i = 6 ∧ j = 7) then -1
    else if (i = 1 ∧ j = 0) ∨ (i = 3 ∧ j = 2) ∨ (i = 5 ∧ j = 4) ∨ (i = 7 ∧ j = 6) then 1
    else 0

/-- Spin polarization involution `K₈` (`K₈² = 1`). -/
def K8_Z : Matrix (Fin 8) (Fin 8) ℤ :=
  Matrix.diagonal ![1, -1, 1, -1, 1, -1, 1, -1]

/-- Helicity involution `Ω₈ = K₈ J₈`. -/
def Omega8_Z : Matrix (Fin 8) (Fin 8) ℤ := K8_Z * J8_spin_Z

/-- OpenGauss T16 non-commutativity witness on `Matrix (Fin 8) (Fin 8) ℤ`:
    the Clifford spin generator `J8_spin_Z` and spin polarization `K8_Z` anticommute. -/
lemma clifford8_matrix_Z_noncomm : ∃ A B : Matrix (Fin 8) (Fin 8) ℤ, A * B ≠ B * A :=
  ⟨J8_spin_Z, K8_Z, by decide⟩

/-- Endogenous Supercolor bridge `G₈ = P₀ D₈ A₈ D₈ P₀` coincides with `G8_Z`. -/
theorem endogenous_supercolor_bridge_theorem :
    let V := casimirV P8_Z A8_Z A8_Z
    let P0 := 1 - V
    let Qp := Qplus P8_Z A8_Z A8_Z
    comm P8_Z G8_Z ≠ 0 ∧
    1 - casimirV P8_Z (A8_Z + G8_Z) (A8_Z + G8_Z) = 0 ∧
    P0 * D8_Z * A8_Z * D8_Z * P0 = G8_Z ∧
    Qp * (D8_Z * G8_Z) * P0 = Qp * (A8_Z * D8_Z) * P0 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Negative-chiral odd supercharge `Q_odd` routing through `P_{0,-}`. -/
def Q_odd_Z : Matrix (Fin 8) (Fin 8) ℤ :=
  let Qp := Qplus P8_Z A8_Z A8_Z
  let Qm := Qminus P8_Z A8_Z A8_Z
  let P0 := 1 - casimirV P8_Z A8_Z A8_Z
  Qp * (A8_Z * D8_Z) * P0 + P0 * D8_Z * Qm

/-- Positive-chiral dual supercharge `Q̃_odd` routing through `P_{0,+}`. -/
def Q_tilde_odd_Z : Matrix (Fin 8) (Fin 8) ℤ :=
  let Qp := Qplus P8_Z A8_Z A8_Z
  let Qm := Qminus P8_Z A8_Z A8_Z
  let P0 := 1 - casimirV P8_Z A8_Z A8_Z
  Qp * D8_Z * P0 + P0 * (D8_Z * A8_Z) * Qm

/-- Full symmetric `N = 2_L ⊕ 2_R = 4` Hermitian supercharge `S_full`. -/
def S_full_Z : Matrix (Fin 8) (Fin 8) ℤ :=
  Q_odd_Z + Q_odd_Z.transpose + Q_tilde_odd_Z + Q_tilde_odd_Z.transpose

/-- Skew-Hermitian Dirac-horizon jump generator `H_hor = J₈ S_full`. -/
def H_hor_Z : Matrix (Fin 8) (Fin 8) ℤ := J8_spin_Z * S_full_Z

/-- Master endogenous Clifford-8 and spin-singlet Andreev synthesis. -/
theorem endogenous_clifford8_singlet_andreev_closure :
    let V := casimirV P8_Z A8_Z A8_Z
    let Qp := Qplus P8_Z A8_Z A8_Z
    let Qm := Qminus P8_Z A8_Z A8_Z
    let P0 := 1 - V
    let sig := sigmaOp P8_Z A8_Z A8_Z
    let Q_odd := Qp * (A8_Z * D8_Z) * P0 + P0 * D8_Z * Qm
    let Delta_plus2_sing := J8_spin_Z * Nplus P8_Z A8_Z
    let Delta_minus2_sing := -Nminus P8_Z A8_Z * J8_spin_Z
    let Delta_BdG_sing := Delta_plus2_sing + Delta_minus2_sing
    let hole_reflected := P0 * comm Delta_minus2_sing Q_odd * Qp
    J8_spin_Z * J8_spin_Z = -1 ∧
    J8_spin_Z.transpose = -J8_spin_Z ∧
    comm sig Q_odd = Q_odd ∧
    Q_odd * Q_odd = Nplus P8_Z A8_Z ∧
    Delta_BdG_sing * Delta_BdG_sing = V ∧
    P0 * (Delta_BdG_sing * Delta_BdG_sing) = 0 ∧
    hole_reflected ≠ 0 ∧
    hole_reflected 5 0 = 1 ∧
    hole_reflected 4 1 = -1 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide,
          by decide, by decide, by decide, by decide⟩

/-- Half-spine starvation vs. full `N = 2_L ⊕ 2_R = 4` supersymmetric closure. -/
theorem dual_chiral_supercharge_closure :
    let P0p := P0_plus P8_Z A8_Z A8_Z
    let P0m := P0_minus P8_Z A8_Z A8_Z
    let sig := sigmaOp P8_Z A8_Z A8_Z
    let Φ := phiOp P8_Z A8_Z A8_Z
    let S_half := Q_odd_Z + Q_odd_Z.transpose
    P0p * Q_odd_Z = 0 ∧ Q_odd_Z * P0p = 0 ∧
    P0p * (S_half ^ 2) = 0 ∧
    P0m * Q_tilde_odd_Z = 0 ∧ Q_tilde_odd_Z * P0m = 0 ∧
    comm sig Q_tilde_odd_Z = Q_tilde_odd_Z ∧
    anticomm Q_odd_Z Q_tilde_odd_Z = 0 ∧
    Q_odd_Z ^ 2 = Nplus P8_Z A8_Z ∧
    Q_tilde_odd_Z ^ 2 = Nplus P8_Z A8_Z ∧
    S_full_Z.transpose = S_full_Z ∧
    S_full_Z ^ 2 = 2 * (1 + Φ + G8_Z) ∧
    S_full_Z ^ 3 = 4 * S_full_Z ∧
    H_hor_Z.transpose = -H_hor_Z ∧
    H_hor_Z ^ 3 = -4 * H_hor_Z := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
          by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- Ring homomorphism `Mat₈(ℤ) →+* Mat₈(ℝ)`. -/
def toMat8R : Matrix (Fin 8) (Fin 8) ℤ →+* Matrix (Fin 8) (Fin 8) ℝ :=
  (Int.castRingHom ℝ).mapMatrix

lemma star_toMat8R (M : Matrix (Fin 8) (Fin 8) ℤ) :
    star (toMat8R M) = toMat8R M.transpose := by
  ext i j
  simp [toMat8R, RingHom.mapMatrix_apply, Matrix.map_apply]

/-- OpenGauss T16 non-commutativity witness on `Matrix (Fin 8) (Fin 8) ℝ`:
    the real embedding of `J8_spin_Z` and `K8_Z` does not commute. -/
lemma clifford8_matrix_R_noncomm : ∃ A B : Matrix (Fin 8) (Fin 8) ℝ, A * B ≠ B * A := by
  refine ⟨toMat8R J8_spin_Z, toMat8R K8_Z, ?_⟩
  intro h
  have h_sub : toMat8R (J8_spin_Z * K8_Z - K8_Z * J8_spin_Z) = 0 := by
    rw [map_sub, map_mul, map_mul, h, sub_self]
  have h01 := congr_fun (congr_fun h_sub 0) 1
  simp only [toMat8R, RingHom.mapMatrix_apply, Matrix.map_apply, Int.coe_castRingHom,
             Matrix.zero_apply, Int.cast_eq_zero] at h01
  revert h01; decide

/-- Spin-singlet thermofield Bogoliubov unitary `U_TFD(χ) = P₀ + cos(χ) V₈ + sin(χ) Ω₈ J`. -/
noncomputable def U_TFD (χ : ℝ) : Matrix (Fin 8) (Fin 8) ℝ :=
  let V := toMat8R (casimirV P8_Z A8_Z A8_Z)
  let P0 := 1 - V
  let G_tfd := toMat8R (Omega8_Z * jOp P8_Z A8_Z A8_Z)
  P0 + Real.cos χ • V + Real.sin χ • G_tfd

/-- Boost anticommutation of `Δ_BdG^sing` and TFD unitarity over `ℝ`. -/
theorem boost_anticomm_and_tfd_unitary (χ : ℝ) :
    let Delta_BdG_sing := J8_spin_Z * Nplus P8_Z A8_Z - Nminus P8_Z A8_Z * J8_spin_Z
    let V_R := toMat8R (casimirV P8_Z A8_Z A8_Z)
    let P0_R := 1 - V_R
    comm J8_spin_Z Delta_BdG_sing = 0 ∧
    anticomm K8_Z Delta_BdG_sing = 0 ∧
    anticomm Omega8_Z Delta_BdG_sing = 0 ∧
    star (U_TFD χ) * U_TFD χ = 1 ∧
    U_TFD χ * P0_R = P0_R := by
  intro Delta_BdG_sing V_R P0_R
  let V_Z := casimirV P8_Z A8_Z A8_Z
  let G_Z := Omega8_Z * jOp P8_Z A8_Z A8_Z
  let V := toMat8R V_Z
  let G := toMat8R G_Z
  have hV_star : star V = V := by
    rw [star_toMat8R, show V_Z.transpose = V_Z by decide]
  have hG_star : star G = -G := by
    rw [star_toMat8R, show G_Z.transpose = -G_Z by decide, map_neg]
  have hVV : V * V = V := by
    rw [← map_mul, show V_Z * V_Z = V_Z by decide]
  have hVG : V * G = G := by
    rw [← map_mul, show V_Z * G_Z = G_Z by decide]
  have hGV : G * V = G := by
    rw [← map_mul, show G_Z * V_Z = G_Z by decide]
  have hGG : G * G = -V := by
    rw [← map_mul, show G_Z * G_Z = -V_Z by decide, map_neg]
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · dsimp [U_TFD]
    change star (1 - V + Real.cos χ • V + Real.sin χ • G) *
        (1 - V + Real.cos χ • V + Real.sin χ • G) = 1
    simp only [star_add, star_sub, star_one, star_smul, star_trivial, hV_star, hG_star]
    have htrig : (Real.cos χ ^ 2 + Real.sin χ ^ 2) • V = V := by
      rw [Real.cos_sq_add_sin_sq, one_smul]
    calc (1 - V + Real.cos χ • V + Real.sin χ • -G) *
           (1 - V + Real.cos χ • V + Real.sin χ • G)
        = 1 - V - (1 - Real.cos χ) • (V - V * V) +
          (Real.cos χ ^ 2 • (V * V) - Real.sin χ ^ 2 • (G * G)) +
          Real.sin χ • ((G - G * V) - (G - V * G)) +
          (Real.cos χ * Real.sin χ) • (V * G - G * V) := by
          simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one,
                     smul_mul_assoc, mul_smul_comm, smul_neg, neg_mul]
          simp only [hVG, hGV, hVV, hGG]
          ext i j
          simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply,
                     Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
          ring
      _ = 1 - V + (Real.cos χ ^ 2 + Real.sin χ ^ 2) • V := by
          simp only [hVV, hGG, hGV, hVG, sub_self, smul_zero, sub_zero, add_zero,
                     smul_neg, sub_neg_eq_add, ← add_smul]
      _ = 1 := by rw [htrig, sub_add_cancel]
  · dsimp [U_TFD, P0_R, V_R]
    change (1 - V + Real.cos χ • V + Real.sin χ • G) * (1 - V) = 1 - V
    calc (1 - V + Real.cos χ • V + Real.sin χ • G) * (1 - V)
        = (1 - V) + (V * V - V) + Real.cos χ • (V - V * V) +
          Real.sin χ • (G - G * V) := by
          simp only [add_mul, sub_mul, mul_sub, one_mul, mul_one,
                     smul_mul_assoc]
          ext i j
          simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
                     Matrix.one_apply, smul_eq_mul]
          ring
      _ = 1 - V := by simp only [hVV, hGV, sub_self, smul_zero, add_zero]

/-- Exact unitary Dirac-horizon propagator `U_t^hor = exp(t J₈ S_full)`. -/
noncomputable def U_hor (t : ℝ) : Matrix (Fin 8) (Fin 8) ℝ :=
  1 + (Real.sin t * Real.cos t) • toMat8R H_hor_Z +
    (Real.sin t ^ 2 / 2) • toMat8R (H_hor_Z ^ 2)

/-- Grade-0 stationarity: any unitary commuting with `Q₊` yields zero horizon leakage. -/
theorem grade_zero_flow_zero_leakage {B : Type*} [Ring B] [StarRing B]
    {Qp P0 Qm U0 piOp : B}
    (hP0_Qp : P0 * Qp = 0) (hQm_Qp : Qm * Qp = 0)
    (hU_Qp : U0 * Qp = Qp * U0) (hpi : Qp * piOp = piOp) :
    P0 * (U0 * piOp * star U0) * Qp = 0 ∧
    Qm * (U0 * piOp * star U0) * Qp = 0 := by
  refine ⟨?_, ?_⟩
  · calc P0 * (U0 * piOp * star U0) * Qp
        = P0 * (U0 * (Qp * piOp) * star U0) * Qp := by rw [hpi]
      _ = (P0 * Qp) * U0 * piOp * star U0 * Qp := by
          rw [← mul_assoc U0 Qp, hU_Qp]; noncomm_ring
      _ = 0 := by rw [hP0_Qp]; noncomm_ring
  · calc Qm * (U0 * piOp * star U0) * Qp
        = Qm * (U0 * (Qp * piOp) * star U0) * Qp := by rw [hpi]
      _ = (Qm * Qp) * U0 * piOp * star U0 * Qp := by
          rw [← mul_assoc U0 Qp, hU_Qp]; noncomm_ring
      _ = 0 := by rw [hQm_Qp]; noncomm_ring

set_option maxHeartbeats 800000 in
/-- All-orders trigonometric horizon leakage: `Φ_t(Q₊) - Φ_t(Q₊)² = B₀(t)* B₀(t) + B₋(t)* B₋(t)`. -/
theorem all_orders_trigonometric_horizon_leakage (t : ℝ) :
    let Qp := toMat8R (Qplus P8_Z A8_Z A8_Z)
    let Qm := toMat8R (Qminus P8_Z A8_Z A8_Z)
    let P0 := toMat8R (1 - casimirV P8_Z A8_Z A8_Z)
    let Xt := U_hor t * Qp * star (U_hor t)
    let Φt := Qp * Xt * Qp
    let B0 := P0 * Xt * Qp
    let Bm := Qm * Xt * Qp
    star (U_hor t) * U_hor t = 1 ∧
    Φt = (Real.cos t ^ 4) • Qp ∧
    star B0 * B0 = (2 * Real.sin t ^ 2 * Real.cos t ^ 6) • Qp ∧
    star Bm * Bm = (Real.sin t ^ 4 * Real.cos t ^ 4) • Qp ∧
    Φt - Φt * Φt = star B0 * B0 + star Bm * Bm := by
  intro Qp Qm P0 Xt Φt B0 Bm
  let Qp_Z := Qplus P8_Z A8_Z A8_Z
  let Qm_Z := Qminus P8_Z A8_Z A8_Z
  let P0_Z := 1 - casimirV P8_Z A8_Z A8_Z
  let H := toMat8R H_hor_Z
  let H2 := toMat8R (H_hor_Z ^ 2)
  have hH_star : star H = -H := by
    rw [star_toMat8R, show H_hor_Z.transpose = -H_hor_Z by decide, map_neg]
  have hH2_star : star H2 = H2 := by
    rw [star_toMat8R, show (H_hor_Z ^ 2).transpose = H_hor_Z ^ 2 by decide]
  have hHH : H * H = H2 := by rw [← map_mul, ← sq]
  have h_m4 : toMat8R (-4 : Matrix (Fin 8) (Fin 8) ℤ) = (-4 : ℝ) • (1 : Matrix (Fin 8) (Fin 8) ℝ) := by
    rw [map_neg, map_ofNat, neg_smul, ← Algebra.algebraMap_eq_smul_one, map_ofNat]
  have h_m2 : toMat8R (-2 : Matrix (Fin 8) (Fin 8) ℤ) = (-2 : ℝ) • (1 : Matrix (Fin 8) (Fin 8) ℝ) := by
    rw [map_neg, map_ofNat, neg_smul, ← Algebra.algebraMap_eq_smul_one, map_ofNat]
  have h_p2 : toMat8R (2 : Matrix (Fin 8) (Fin 8) ℤ) = (2 : ℝ) • (1 : Matrix (Fin 8) (Fin 8) ℝ) := by
    rw [map_ofNat, ← Algebra.algebraMap_eq_smul_one, map_ofNat]
  have h_p4 : toMat8R (4 : Matrix (Fin 8) (Fin 8) ℤ) = (4 : ℝ) • (1 : Matrix (Fin 8) (Fin 8) ℝ) := by
    rw [map_ofNat, ← Algebra.algebraMap_eq_smul_one, map_ofNat]
  have hHH2 : H * H2 = (-4 : ℝ) • H := by
    have h : H * H2 = toMat8R (-4 * H_hor_Z) := by
      rw [← map_mul, show H_hor_Z * H_hor_Z ^ 2 = -4 * H_hor_Z by decide]
    rw [h, map_mul, h_m4, smul_mul_assoc, one_mul]
  have hH2H : H2 * H = (-4 : ℝ) • H := by
    have h : H2 * H = toMat8R (-4 * H_hor_Z) := by
      rw [← map_mul, show H_hor_Z ^ 2 * H_hor_Z = -4 * H_hor_Z by decide]
    rw [h, map_mul, h_m4, smul_mul_assoc, one_mul]
  have hH2H2 : H2 * H2 = (-4 : ℝ) • H2 := by
    have h : H2 * H2 = toMat8R (-4 * H_hor_Z ^ 2) := by
      rw [← map_mul, show H_hor_Z ^ 2 * H_hor_Z ^ 2 = -4 * H_hor_Z ^ 2 by decide]
    rw [h, map_mul, h_m4, smul_mul_assoc, one_mul]
  have hQp_star : star Qp = Qp := by
    rw [star_toMat8R, show Qp_Z.transpose = Qp_Z by decide]
  have hQp_idem : Qp * Qp = Qp := by
    rw [← map_mul, show Qp_Z * Qp_Z = Qp_Z by decide]
  have hQp_H_Qp : Qp * H * Qp = 0 := by
    rw [← map_mul, ← map_mul, show Qp_Z * H_hor_Z * Qp_Z = 0 by decide, map_zero]
  have hQp_H2_Qp : Qp * H2 * Qp = (-2 : ℝ) • Qp := by
    have h : Qp * H2 * Qp = toMat8R (-2 * Qp_Z) := by
      rw [← map_mul, ← map_mul, show Qp_Z * H_hor_Z ^ 2 * Qp_Z = -2 * Qp_Z by decide]
    rw [h, map_mul, h_m2, smul_mul_assoc, one_mul]
  have hP0_Qp : P0 * Qp = 0 := by
    rw [← map_mul, show P0_Z * Qp_Z = 0 by decide, map_zero]
  have hP0_H2_Qp : P0 * H2 * Qp = 0 := by
    rw [← map_mul, ← map_mul, show P0_Z * H_hor_Z ^ 2 * Qp_Z = 0 by decide, map_zero]
  have hQp_H_P0_H_Qp : (Qp * -H * P0) * (P0 * H * Qp) = (2 : ℝ) • Qp := by
    have h : (Qp * -H * P0) * (P0 * H * Qp) = toMat8R (2 * Qp_Z) := by
      rw [← map_neg, ← map_mul, ← map_mul, ← map_mul, ← map_mul, ← map_mul,
          show (Qp_Z * -H_hor_Z * P0_Z) * (P0_Z * H_hor_Z * Qp_Z) = 2 * Qp_Z by decide]
    rw [h, map_mul, h_p2, smul_mul_assoc, one_mul]
  have hQm_Qp : Qm * Qp = 0 := by
    rw [← map_mul, show Qm_Z * Qp_Z = 0 by decide, map_zero]
  have hQm_H_Qp : Qm * H * Qp = 0 := by
    rw [← map_mul, ← map_mul, show Qm_Z * H_hor_Z * Qp_Z = 0 by decide, map_zero]
  have hQp_H2_Qm_H2_Qp : (Qp * H2 * Qm) * (Qm * H2 * Qp) = (4 : ℝ) • Qp := by
    have h : (Qp * H2 * Qm) * (Qm * H2 * Qp) = toMat8R (4 * Qp_Z) := by
      rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, ← map_mul,
          show (Qp_Z * H_hor_Z ^ 2 * Qm_Z) * (Qm_Z * H_hor_Z ^ 2 * Qp_Z) = 4 * Qp_Z by decide]
    rw [h, map_mul, h_p4, smul_mul_assoc, one_mul]
  have hQp_U_Qp : Qp * U_hor t * Qp = (Real.cos t ^ 2) • Qp := by
    dsimp [U_hor]
    have hlin : Qp * (1 + (Real.sin t * Real.cos t) • H + (Real.sin t ^ 2 / 2) • H2) * Qp =
        Qp * Qp + (Real.sin t * Real.cos t) • (Qp * H * Qp) +
          (Real.sin t ^ 2 / 2) • (Qp * H2 * Qp) := by
      simp only [mul_add, add_mul, mul_one, smul_mul_assoc, mul_smul_comm]
    rw [hlin, hQp_idem, hQp_H_Qp, hQp_H2_Qp, smul_zero, add_zero, smul_smul]
    have htrig : 1 + Real.sin t ^ 2 / 2 * (-2) = Real.cos t ^ 2 := by
      linarith [Real.cos_sq_add_sin_sq t]
    rw [← htrig, add_smul, one_smul]
  have hQp_Ustar_Qp : Qp * star (U_hor t) * Qp = (Real.cos t ^ 2) • Qp := by
    have h := congrArg star hQp_U_Qp
    simp only [star_mul, star_smul, star_trivial, hQp_star, ← mul_assoc] at h
    exact h
  have hP0_U_Qp : P0 * U_hor t * Qp = (Real.sin t * Real.cos t) • (P0 * H * Qp) := by
    dsimp [U_hor]
    have hlin : P0 * (1 + (Real.sin t * Real.cos t) • H + (Real.sin t ^ 2 / 2) • H2) * Qp =
        P0 * Qp + (Real.sin t * Real.cos t) • (P0 * H * Qp) +
          (Real.sin t ^ 2 / 2) • (P0 * H2 * Qp) := by
      simp only [mul_add, add_mul, mul_one, smul_mul_assoc, mul_smul_comm]
    rw [hlin, hP0_Qp, hP0_H2_Qp, zero_add, smul_zero, add_zero]
  have hQm_U_Qp : Qm * U_hor t * Qp = (Real.sin t ^ 2 / 2) • (Qm * H2 * Qp) := by
    dsimp [U_hor]
    have hlin : Qm * (1 + (Real.sin t * Real.cos t) • H + (Real.sin t ^ 2 / 2) • H2) * Qp =
        Qm * Qp + (Real.sin t * Real.cos t) • (Qm * H * Qp) +
          (Real.sin t ^ 2 / 2) • (Qm * H2 * Qp) := by
      simp only [mul_add, add_mul, mul_one, smul_mul_assoc, mul_smul_comm]
    rw [hlin, hQm_Qp, hQm_H_Qp, zero_add, smul_zero, zero_add]
  have hΦt : Φt = (Real.cos t ^ 4) • Qp := by
    dsimp [Φt, Xt]
    calc Qp * (U_hor t * Qp * star (U_hor t)) * Qp
        = (Qp * U_hor t * Qp) * (Qp * star (U_hor t) * Qp) := by
          nth_rw 2 [← hQp_idem]; noncomm_ring
      _ = ((Real.cos t ^ 2) • Qp) * ((Real.cos t ^ 2) • Qp) := by
          rw [hQp_U_Qp, hQp_Ustar_Qp]
      _ = (Real.cos t ^ 4) • Qp := by
          rw [smul_mul_assoc, mul_smul_comm, smul_smul, hQp_idem]; ring_nf
  have hB0_sq : star B0 * B0 = (2 * Real.sin t ^ 2 * Real.cos t ^ 6) • Qp := by
    have hB0_eval : B0 = (Real.sin t * Real.cos t ^ 3) • (P0 * H * Qp) := by
      dsimp [B0, Xt]
      calc P0 * (U_hor t * Qp * star (U_hor t)) * Qp
          = (P0 * U_hor t * Qp) * (Qp * star (U_hor t) * Qp) := by
            nth_rw 1 [← hQp_idem]; noncomm_ring
        _ = ((Real.sin t * Real.cos t) • (P0 * H * Qp)) * ((Real.cos t ^ 2) • Qp) := by
            rw [hP0_U_Qp, hQp_Ustar_Qp]
        _ = (Real.sin t * Real.cos t ^ 3) • (P0 * H * Qp) := by
            rw [smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc (P0 * H), hQp_idem]; congr 1; ring
    have hP0_star : star P0 = P0 := by
      rw [star_toMat8R, show P0_Z.transpose = P0_Z by decide]
    rw [hB0_eval, star_smul, star_trivial, star_mul, star_mul, hQp_star, hH_star, hP0_star,
        smul_mul_assoc, mul_smul_comm, smul_smul, ← mul_assoc Qp (-H) P0, hQp_H_P0_H_Qp, smul_smul]
    congr 1; ring
  have hBm_sq : star Bm * Bm = (Real.sin t ^ 4 * Real.cos t ^ 4) • Qp := by
    have hBm_eval : Bm = (Real.sin t ^ 2 * Real.cos t ^ 2 / 2) • (Qm * H2 * Qp) := by
      dsimp [Bm, Xt]
      calc Qm * (U_hor t * Qp * star (U_hor t)) * Qp
          = (Qm * U_hor t * Qp) * (Qp * star (U_hor t) * Qp) := by
            nth_rw 1 [← hQp_idem]; noncomm_ring
        _ = ((Real.sin t ^ 2 / 2) • (Qm * H2 * Qp)) * ((Real.cos t ^ 2) • Qp) := by
            rw [hQm_U_Qp, hQp_Ustar_Qp]
        _ = (Real.sin t ^ 2 * Real.cos t ^ 2 / 2) • (Qm * H2 * Qp) := by
            rw [smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc, hQp_idem]; ring_nf
    have hQm_star : star Qm = Qm := by
      rw [star_toMat8R, show Qm_Z.transpose = Qm_Z by decide]
    rw [hBm_eval, star_smul, star_trivial, star_mul, star_mul, hQp_star, hH2_star, hQm_star,
        smul_mul_assoc, mul_smul_comm, smul_smul, ← mul_assoc Qp H2 Qm, hQp_H2_Qm_H2_Qp, smul_smul]
    congr 1; ring
  refine ⟨?_, hΦt, hB0_sq, hBm_sq, ?_⟩
  · dsimp [U_hor]
    change star (1 + (Real.sin t * Real.cos t) • H + (Real.sin t ^ 2 / 2) • H2) *
        (1 + (Real.sin t * Real.cos t) • H + (Real.sin t ^ 2 / 2) • H2) = 1
    simp only [star_add, star_one, star_smul, star_trivial, hH_star, hH2_star]
    have hlin : (1 + (Real.sin t * Real.cos t) • -H + (Real.sin t ^ 2 / 2) • H2) *
        (1 + (Real.sin t * Real.cos t) • H + (Real.sin t ^ 2 / 2) • H2) =
        1 + (Real.sin t ^ 2 - (Real.sin t * Real.cos t) ^ 2 + Real.sin t ^ 4 / 4 * (-4)) • H2 := by
      simp only [add_mul, mul_add, one_mul, mul_one, neg_mul, mul_neg,
                 smul_mul_assoc, mul_smul_comm, smul_smul, smul_neg, neg_smul,
                 hHH, hHH2, hH2H, hH2H2]
      ext i j
      simp only [Matrix.add_apply, Matrix.neg_apply, Matrix.smul_apply,
                 Matrix.one_apply, smul_eq_mul]
      ring
    rw [hlin]
    have hc : Real.sin t ^ 2 - (Real.sin t * Real.cos t) ^ 2 + Real.sin t ^ 4 / 4 * (-4) = 0 := by
      have hsc : Real.cos t ^ 2 + Real.sin t ^ 2 = 1 := Real.cos_sq_add_sin_sq t
      nlinarith
    rw [hc, zero_smul, add_zero]
  · rw [hΦt, hB0_sq, hBm_sq, smul_mul_assoc, mul_smul_comm, smul_smul, hQp_idem,
        ← sub_smul, ← add_smul]
    have htrig : Real.cos t ^ 4 - Real.cos t ^ 4 * Real.cos t ^ 4 =
        2 * Real.sin t ^ 2 * Real.cos t ^ 6 + Real.sin t ^ 4 * Real.cos t ^ 4 := by
      have hsc : Real.cos t ^ 2 + Real.sin t ^ 2 = 1 := Real.cos_sq_add_sin_sq t
      calc Real.cos t ^ 4 - Real.cos t ^ 4 * Real.cos t ^ 4
          = Real.cos t ^ 4 * ((Real.cos t ^ 2 + Real.sin t ^ 2) ^ 2 - Real.cos t ^ 4) := by
            rw [hsc]; ring
        _ = 2 * Real.sin t ^ 2 * Real.cos t ^ 6 + Real.sin t ^ 4 * Real.cos t ^ 4 := by ring
    rw [htrig]

/-- Doubled spin-chiral GKSL jump operators `2 L_{σ,χ}` over `ℤ`. -/
def twoL_up_plus (S_pol : Matrix (Fin 8) (Fin 8) ℤ) : Matrix (Fin 8) (Fin 8) ℤ :=
  (1 + S_pol) * (1 - casimirV P8_Z A8_Z A8_Z) * Q_tilde_odd_Z.transpose * Qplus P8_Z A8_Z A8_Z

def twoL_dn_plus (S_pol : Matrix (Fin 8) (Fin 8) ℤ) : Matrix (Fin 8) (Fin 8) ℤ :=
  (1 - S_pol) * (1 - casimirV P8_Z A8_Z A8_Z) * Q_tilde_odd_Z.transpose * Qplus P8_Z A8_Z A8_Z

def twoL_up_minus (S_pol : Matrix (Fin 8) (Fin 8) ℤ) : Matrix (Fin 8) (Fin 8) ℤ :=
  (1 + S_pol) * (1 - casimirV P8_Z A8_Z A8_Z) * Q_odd_Z.transpose * Qplus P8_Z A8_Z A8_Z

def twoL_dn_minus (S_pol : Matrix (Fin 8) (Fin 8) ℤ) : Matrix (Fin 8) (Fin 8) ℤ :=
  (1 - S_pol) * (1 - casimirV P8_Z A8_Z A8_Z) * Q_odd_Z.transpose * Qplus P8_Z A8_Z A8_Z

/-- Four-channel spin-chiral GKSL Kraus completeness in both `Ω₈` and `K₈` bases. -/
theorem four_channel_spin_chiral_kraus_completeness :
    let Qp := Qplus P8_Z A8_Z A8_Z
    (twoL_up_plus Omega8_Z).transpose * twoL_up_plus Omega8_Z +
      (twoL_dn_plus Omega8_Z).transpose * twoL_dn_plus Omega8_Z +
      (twoL_up_minus Omega8_Z).transpose * twoL_up_minus Omega8_Z +
      (twoL_dn_minus Omega8_Z).transpose * twoL_dn_minus Omega8_Z = 8 * Qp ∧
    (twoL_up_plus Omega8_Z).transpose * twoL_dn_plus Omega8_Z = 0 ∧
    (twoL_up_plus Omega8_Z).transpose * twoL_up_minus Omega8_Z = 0 ∧
    (twoL_up_plus K8_Z).transpose * twoL_up_plus K8_Z +
      (twoL_dn_plus K8_Z).transpose * twoL_dn_plus K8_Z +
      (twoL_up_minus K8_Z).transpose * twoL_up_minus K8_Z +
      (twoL_dn_minus K8_Z).transpose * twoL_dn_minus K8_Z = 8 * Qp ∧
    twoL_up_plus K8_Z 2 0 = 2 ∧
    twoL_dn_plus K8_Z 3 1 = 2 ∧
    twoL_up_minus K8_Z 4 0 = 2 ∧
    twoL_dn_minus K8_Z 5 1 = 2 := by
  refine ⟨by decide, by decide, by decide, by decide,
          by decide, by decide, by decide, by decide⟩

/-! ### Part III: Cosmological Condensate & EoS (`R₀ ≺ … ≺ R₉`) -/

/-- Pregeometric spacetime vanishes iff `V = 0` (`N₊ = 0 ∧ N₋ = 0`). -/
theorem pregeometric_spacetime_vanishes_iff_V_zero {B : Type*} [Ring B] [StarRing B]
    {P A : B} (hP : delta P = 0) (hP_star : star P = P)
    (hfaith3 : ∀ Y1 Y2 Y3 : B, star Y1 * Y1 + star Y2 * Y2 + star Y3 * Y3 = 0 → Y1 = 0) :
    let Np := Nplus P A
    let Nm := Nminus P (star A)
    let Qp := Qplus P A (star A)
    let Qm := Qminus P A (star A)
    let V := casimirV P A (star A)
    (V = 0 ↔ (Np = 0 ∧ Nm = 0)) ∧
    (V = 0 → ∀ X : B, Qp * X * Qm = 0) := by
  intro Np Nm Qp Qm V
  have hNp_star : star Np = Nm := by
    dsimp [Np, Nm, Nplus, Nminus]; simp only [star_mul, star_sub, star_one, hP_star, mul_assoc]
  have hNm_star : star Nm = Np := by rw [← hNp_star, star_star]
  have hQp_star : star Qp = Qp := by
    dsimp [Qp, Qplus]; rw [star_mul, hNm_star, hNp_star]
  have hQm_star : star Qm = Qm := by
    dsimp [Qm, Qminus]; rw [star_mul, hNp_star, hNm_star]
  have hV_iff : V = 0 ↔ (Np = 0 ∧ Nm = 0) := by
    constructor
    · intro hV
      have hsumQ : star Qp * Qp + star Qm * Qm + star (0 : B) * 0 = 0 := by
        rw [hQp_star, hQm_star, star_zero, mul_zero, add_zero]
        calc Qp * Qp + Qm * Qm
            = (Qp + Qm) * (Qp + Qm) - (Qp * Qm + Qm * Qp) := by noncomm_ring
          _ = V * V - (0 + 0) := by
              rw [Qplus_mul_Qminus hP, Qminus_mul_Qplus hP]; rfl
          _ = 0 := by rw [hV]; noncomm_ring
      have hQp0 : Qp = 0 := hfaith3 Qp Qm 0 hsumQ
      have hNm0 : Nm = 0 := by
        apply hfaith3 Nm 0 0
        rw [star_zero, mul_zero, add_zero, add_zero, hNm_star]
        exact hQp0
      have hNp0 : Np = 0 := by rw [← hNm_star, hNm0, star_zero]
      exact ⟨hNp0, hNm0⟩
    · rintro ⟨hNp0, hNm0⟩
      have hNp0' : Nplus P A = 0 := hNp0
      have hNm0' : Nminus P (star A) = 0 := hNm0
      dsimp [V, casimirV, Qp, Qm, Qplus, Qminus]
      rw [hNp0', hNm0']; noncomm_ring
  refine ⟨hV_iff, ?_⟩
  intro hV X
  obtain ⟨hNp0, _⟩ := hV_iff.mp hV
  have hNp0' : Nplus P A = 0 := hNp0
  dsimp [Qp, Qplus]
  rw [hNp0', zero_mul, zero_mul, zero_mul]

/-- Hyperbolic Lorentz boost generator in `(t, x)`. -/
def K_boost2 (R : Type*) [CommRing R] : Matrix (Fin 2) (Fin 2) R := !![0, 1; 1, 0]

/-- Mixed stress-energy tensor `T^μ_ν = [[-ρ, f], [-f, p]]`. -/
def stressTensor {R : Type*} [CommRing R] (ρ p f : R) : Matrix (Fin 2) (Fin 2) R :=
  !![-ρ, f; -f, p]

/-- Lorentz boost invariance forces `f = 0` and Dark Energy EoS `p = -ρ` (`w = -1`). -/
theorem lorentz_boost_invariance_forces_dark_energy_eos {R : Type*} [CommRing R] [Invertible (2 : R)]
    (ρ p f : R) :
    comm (K_boost2 R) (stressTensor ρ p f) = 0 ↔ (f = 0 ∧ p = -ρ) := by
  constructor
  · intro hcomm
    have h00 := congr_fun (congr_fun hcomm 0) 0
    have h01 := congr_fun (congr_fun hcomm 0) 1
    simp only [comm, K_boost2, stressTensor, Matrix.sub_apply, Matrix.mul_apply,
               Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
               Matrix.cons_val_one, Matrix.zero_apply] at h00 h01
    have hf2 : (2 : R) * f = 0 := by linear_combination -h00
    have hf : f = 0 := by
      calc f = ⅟(2 : R) * ((2 : R) * f) := by rw [← mul_assoc, invOf_mul_self, one_mul]
        _ = 0 := by rw [hf2, mul_zero]
    have hp : p = -ρ := by linear_combination h01
    exact ⟨hf, hp⟩
  · rintro ⟨rfl, rfl⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [comm, K_boost2, stressTensor]

/-- Sector-selective boost breaking on `Q₊ ⊕ Q₋` and exact photon insulation on `P₀`. -/
theorem sector_selective_boost_breaking_and_photon_shielding {B : Type*} [Ring B] [StarRing B]
    {P A_tilde J_spin K_boost : B} (hP : delta P = 0) (hP_star : star P = P)
    (hA_star : star A_tilde = A_tilde)
    (hfaith3 : ∀ Y1 Y2 Y3 : B, star Y1 * Y1 + star Y2 * Y2 + star Y3 * Y3 = 0 → Y1 = 0)
    (hJ_sq : J_spin * J_spin = -1) (hK_sq : K_boost * K_boost = 1)
    (hJK_anti : J_spin * K_boost + K_boost * J_spin = 0)
    (hJ_P : J_spin * P = P * J_spin) (hJ_A : J_spin * A_tilde = A_tilde * J_spin)
    (hK_P : K_boost * P = P * K_boost) (hK_A : K_boost * A_tilde = A_tilde * K_boost)
    (hV : delta (casimirV P A_tilde A_tilde) = 0) (A_gamma : B) :
    let Np := Nplus P A_tilde
    let Nm := Nminus P A_tilde
    let V := casimirV P A_tilde A_tilde
    let P0 := 1 - V
    let Delta_BdG_sing := -Np * J_spin + J_spin * Nm
    comm J_spin Delta_BdG_sing = 0 ∧
    anticomm K_boost Delta_BdG_sing = 0 ∧
    K_boost * Delta_BdG_sing * K_boost = -Delta_BdG_sing ∧
    Delta_BdG_sing * Delta_BdG_sing = V ∧
    comm K_boost V = 0 ∧
    P0 * Delta_BdG_sing = 0 ∧
    Delta_BdG_sing * P0 = 0 ∧
    comm Delta_BdG_sing (P0 * A_gamma * P0) = 0 ∧
    comm V (P0 * A_gamma * P0) = 0 := by
  intro Np Nm V P0 Delta_BdG_sing
  have hNp_star : star Np = Nm := by
    dsimp [Np, Nm, Nplus, Nminus]
    simp only [star_mul, star_sub, star_one, hP_star, hA_star, mul_assoc]
  have hNm_star : star Nm = Np := by rw [← hNp_star, star_star]
  have hV_star : star V = V := by
    change star (Np * Nm + Nm * Np) = Np * Nm + Nm * Np
    simp only [star_add, star_mul, hNp_star, hNm_star]
  have hJ_Np : J_spin * Np = Np * J_spin := by
    dsimp [Np, Nplus]
    calc J_spin * (P * A_tilde * (1 - P))
        = (J_spin * P) * A_tilde * (1 - P) := by noncomm_ring
      _ = P * (J_spin * A_tilde) * (1 - P) := by rw [hJ_P]; noncomm_ring
      _ = P * A_tilde * (J_spin - J_spin * P) := by rw [hJ_A]; noncomm_ring
      _ = P * A_tilde * (1 - P) * J_spin := by rw [hJ_P]; noncomm_ring
  have hJ_Nm : J_spin * Nm = Nm * J_spin := by
    dsimp [Nm, Nminus]
    calc J_spin * ((1 - P) * A_tilde * P)
        = (J_spin - J_spin * P) * A_tilde * P := by noncomm_ring
      _ = (1 - P) * (J_spin * A_tilde) * P := by rw [hJ_P]; noncomm_ring
      _ = (1 - P) * A_tilde * (J_spin * P) := by rw [hJ_A]; noncomm_ring
      _ = (1 - P) * A_tilde * P * J_spin := by rw [hJ_P]; noncomm_ring
  have hK_Np : K_boost * Np = Np * K_boost := by
    dsimp [Np, Nplus]
    calc K_boost * (P * A_tilde * (1 - P))
        = (K_boost * P) * A_tilde * (1 - P) := by noncomm_ring
      _ = P * (K_boost * A_tilde) * (1 - P) := by rw [hK_P]; noncomm_ring
      _ = P * A_tilde * (K_boost - K_boost * P) := by rw [hK_A]; noncomm_ring
      _ = P * A_tilde * (1 - P) * K_boost := by rw [hK_P]; noncomm_ring
  have hK_Nm : K_boost * Nm = Nm * K_boost := by
    dsimp [Nm, Nminus]
    calc K_boost * ((1 - P) * A_tilde * P)
        = (K_boost - K_boost * P) * A_tilde * P := by noncomm_ring
      _ = (1 - P) * (K_boost * A_tilde) * P := by rw [hK_P]; noncomm_ring
      _ = (1 - P) * A_tilde * (K_boost * P) := by rw [hK_A]; noncomm_ring
      _ = (1 - P) * A_tilde * P * K_boost := by rw [hK_P]; noncomm_ring
  have hKJ : K_boost * J_spin = -J_spin * K_boost := by
    calc K_boost * J_spin = (J_spin * K_boost + K_boost * J_spin) - J_spin * K_boost := by
          noncomm_ring
      _ = -J_spin * K_boost := by rw [hJK_anti]; noncomm_ring
  have hanti_K : anticomm K_boost Delta_BdG_sing = 0 := by
    dsimp [anticomm, Delta_BdG_sing]
    calc K_boost * (-Np * J_spin + J_spin * Nm) + (-Np * J_spin + J_spin * Nm) * K_boost
        = -(K_boost * Np) * J_spin + (K_boost * J_spin) * Nm -
          Np * (J_spin * K_boost) + J_spin * (Nm * K_boost) := by noncomm_ring
      _ = -Np * (K_boost * J_spin + J_spin * K_boost) +
          (K_boost * J_spin + J_spin * K_boost) * Nm := by
          rw [hK_Np, ← hK_Nm]; noncomm_ring
      _ = 0 := by rw [hKJ]; noncomm_ring
  have hK_conj : K_boost * Delta_BdG_sing * K_boost = -Delta_BdG_sing := by
    have h1 : K_boost * Delta_BdG_sing = -Delta_BdG_sing * K_boost := by
      calc K_boost * Delta_BdG_sing
          = anticomm K_boost Delta_BdG_sing - Delta_BdG_sing * K_boost := by
            dsimp [anticomm]; noncomm_ring
        _ = -Delta_BdG_sing * K_boost := by rw [hanti_K]; noncomm_ring
    calc K_boost * Delta_BdG_sing * K_boost
        = -Delta_BdG_sing * (K_boost * K_boost) := by rw [h1]; noncomm_ring
      _ = -Delta_BdG_sing := by rw [hK_sq]; noncomm_ring
  have hsq : Delta_BdG_sing * Delta_BdG_sing = V := by
    dsimp [Delta_BdG_sing, V, casimirV, Qplus, Qminus, Np, Nm]
    have h1 : (-Np * J_spin) * (-Np * J_spin) = 0 := by
      calc (-Np * J_spin) * (-Np * J_spin)
          = Np * (J_spin * Np) * J_spin := by noncomm_ring
        _ = (Np * Np) * J_spin * J_spin := by rw [hJ_Np]; noncomm_ring
        _ = 0 := by dsimp [Np]; rw [Nplus_sq hP]; noncomm_ring
    have h2 : (J_spin * Nm) * (J_spin * Nm) = 0 := by
      calc (J_spin * Nm) * (J_spin * Nm)
          = J_spin * (Nm * J_spin) * Nm := by noncomm_ring
        _ = J_spin * (J_spin * Nm) * Nm := by rw [hJ_Nm]
        _ = J_spin * J_spin * (Nm * Nm) := by noncomm_ring
        _ = 0 := by dsimp [Nm]; rw [Nminus_sq hP]; noncomm_ring
    have h3 : (-Np * J_spin) * (J_spin * Nm) = Np * Nm := by
      calc (-Np * J_spin) * (J_spin * Nm)
          = -Np * (J_spin * J_spin) * Nm := by noncomm_ring
        _ = Np * Nm := by rw [hJ_sq]; noncomm_ring
    have h4 : (J_spin * Nm) * (-Np * J_spin) = Nm * Np := by
      calc (J_spin * Nm) * (-Np * J_spin)
          = -J_spin * Nm * (Np * J_spin) := by noncomm_ring
        _ = -J_spin * Nm * (J_spin * Np) := by rw [hJ_Np]
        _ = -J_spin * (Nm * J_spin) * Np := by noncomm_ring
        _ = -J_spin * (J_spin * Nm) * Np := by rw [hJ_Nm]
        _ = -(J_spin * J_spin) * (Nm * Np) := by noncomm_ring
        _ = Nm * Np := by rw [hJ_sq]; noncomm_ring
    calc (-Np * J_spin + J_spin * Nm) * (-Np * J_spin + J_spin * Nm)
        = (-Np * J_spin) * (-Np * J_spin) + (-Np * J_spin) * (J_spin * Nm) +
          (J_spin * Nm) * (-Np * J_spin) + (J_spin * Nm) * (J_spin * Nm) := by noncomm_ring
      _ = Np * Nm + Nm * Np := by rw [h1, h2, h3, h4]; abel
  have h1V_V : P0 * V = 0 := by
    dsimp [P0]
    calc (1 - V) * V = -delta V := by dsimp [delta]; noncomm_ring
      _ = 0 := by rw [hV, neg_zero]
  have hV_1V : V * P0 = 0 := by
    dsimp [P0]
    calc V * (1 - V) = -delta V := by dsimp [delta]; noncomm_ring
      _ = 0 := by rw [hV, neg_zero]
  have hfaith1 : ∀ Y : B, star Y * Y = 0 → Y = 0 := fun Y hY =>
    hfaith3 Y 0 0 (by simpa using hY)
  have hVP : V * P = Np * Nm := by
    dsimp [V, casimirV, Qplus, Qminus, Np, Nm]
    calc (Np * Nm + Nm * Np) * P = Np * (Nm * P) + Nm * (Np * P) := by noncomm_ring
      _ = Np * Nm := by dsimp [Np, Nm]; rw [Nminus_mul_P hP, Nplus_mul_P hP]; noncomm_ring
  have hP0_Np : P0 * Np = 0 := by
    let Y := Nm * P0
    have hP0_star : star P0 = P0 := by dsimp [P0]; rw [star_sub, star_one, hV_star]
    have hY_star : star Y = P0 * Np := by dsimp [Y]; rw [star_mul, hP0_star, hNm_star]
    have hYY : star Y * Y = 0 := by
      rw [hY_star]; dsimp [Y]
      calc P0 * Np * (Nm * P0) = P0 * (Np * Nm) * P0 := by noncomm_ring
        _ = (P0 * V) * P * P0 := by rw [← hVP]; noncomm_ring
        _ = 0 := by rw [h1V_V]; noncomm_ring
    rw [← hY_star, hfaith1 Y hYY, star_zero]
  have hP0_Nm : P0 * Nm = 0 := by
    let Z := Np * P0
    have hP0_star : star P0 = P0 := by dsimp [P0]; rw [star_sub, star_one, hV_star]
    have hZ_star : star Z = P0 * Nm := by dsimp [Z]; rw [star_mul, hP0_star, hNp_star]
    have hZZ : star Z * Z = 0 := by
      rw [hZ_star]; dsimp [Z]
      have hQm_eq : Nm * Np = V * (1 - P) := by
        calc Nm * Np = V - Np * Nm := by dsimp [V, casimirV, Qplus, Qminus, Np, Nm]; noncomm_ring
          _ = V * (1 - P) := by rw [← hVP]; noncomm_ring
      calc P0 * Nm * (Np * P0) = P0 * (Nm * Np) * P0 := by noncomm_ring
        _ = (P0 * V) * (1 - P) * P0 := by rw [hQm_eq]; noncomm_ring
        _ = 0 := by rw [h1V_V]; noncomm_ring
    rw [← hZ_star, hfaith1 Z hZZ, star_zero]
  have hNp_P0 : Np * P0 = 0 := by
    have hP0_star : star P0 = P0 := by dsimp [P0]; rw [star_sub, star_one, hV_star]
    calc Np * P0 = star (P0 * Nm) := by rw [star_mul, hNm_star, hP0_star]
      _ = 0 := by rw [hP0_Nm, star_zero]
  have hNm_P0 : Nm * P0 = 0 := by
    have hP0_star : star P0 = P0 := by dsimp [P0]; rw [star_sub, star_one, hV_star]
    calc Nm * P0 = star (P0 * Np) := by rw [star_mul, hNp_star, hP0_star]
      _ = 0 := by rw [hP0_Np, star_zero]
  have hP0_Delta : P0 * Delta_BdG_sing = 0 := by
    dsimp [Delta_BdG_sing]
    calc P0 * (-Np * J_spin + J_spin * Nm)
        = -(P0 * Np) * J_spin + P0 * (Nm * J_spin) := by rw [hJ_Nm]; noncomm_ring
      _ = -(P0 * Np) * J_spin + (P0 * Nm) * J_spin := by noncomm_ring
      _ = 0 := by rw [hP0_Np, hP0_Nm]; noncomm_ring
  have hDelta_P0 : Delta_BdG_sing * P0 = 0 := by
    dsimp [Delta_BdG_sing]
    calc (-Np * J_spin + J_spin * Nm) * P0
        = -(J_spin * Np) * P0 + J_spin * (Nm * P0) := by rw [hJ_Np]; noncomm_ring
      _ = -J_spin * (Np * P0) + J_spin * (Nm * P0) := by noncomm_ring
      _ = 0 := by rw [hNp_P0, hNm_P0]; noncomm_ring
  refine ⟨?_, hanti_K, hK_conj, hsq, ?_, hP0_Delta, hDelta_P0, ?_, ?_⟩
  · dsimp [comm, Delta_BdG_sing]
    calc J_spin * (-Np * J_spin + J_spin * Nm) - (-Np * J_spin + J_spin * Nm) * J_spin
        = -(J_spin * Np) * J_spin + J_spin * J_spin * Nm +
          Np * J_spin * J_spin - J_spin * (Nm * J_spin) := by noncomm_ring
      _ = 0 := by rw [hJ_Np, ← hJ_Nm]; noncomm_ring
  · dsimp [comm, V, casimirV, Qplus, Qminus, Np, Nm]
    calc K_boost * (Np * Nm + Nm * Np) - (Np * Nm + Nm * Np) * K_boost
        = (K_boost * Np) * Nm + (K_boost * Nm) * Np -
          Np * (Nm * K_boost) - Nm * (Np * K_boost) := by noncomm_ring
      _ = (Np * K_boost) * Nm + (Nm * K_boost) * Np -
          Np * (Nm * K_boost) - Nm * (Np * K_boost) := by rw [hK_Np, hK_Nm]
      _ = Np * (K_boost * Nm - Nm * K_boost) +
          Nm * (K_boost * Np - Np * K_boost) := by noncomm_ring
      _ = 0 := by rw [hK_Nm, hK_Np]; noncomm_ring
  · dsimp [comm]
    calc Delta_BdG_sing * (P0 * A_gamma * P0) - (P0 * A_gamma * P0) * Delta_BdG_sing
        = (Delta_BdG_sing * P0) * A_gamma * P0 - P0 * A_gamma * (P0 * Delta_BdG_sing) := by
          noncomm_ring
      _ = 0 := by rw [hDelta_P0, hP0_Delta]; noncomm_ring
  · dsimp [comm]
    calc V * (P0 * A_gamma * P0) - (P0 * A_gamma * P0) * V
        = (V * P0) * A_gamma * P0 - P0 * A_gamma * (P0 * V) := by noncomm_ring
      _ = 0 := by rw [hV_1V, h1V_V]; noncomm_ring

/-- Relativistic pressure-to-energy-density ratio `w(k, m) = k² / (3 (k² + m²))`. -/
noncomputable def eosRatio (k m : ℝ) : ℝ := k ^ 2 / (3 * (k ^ 2 + m ^ 2))

/-- Cold Bogoliubov quasiparticles (`w → 0`) vs. hot Goldstone radiation (`w = 1/3`). -/
theorem bogoliubov_cold_matter_vs_goldstone_radiation_eos :
    (∀ k : ℝ, k ≠ 0 → eosRatio k 0 = 1 / 3) ∧
    (∀ m : ℝ, eosRatio 0 m = 0) ∧
    (∀ k m : ℝ, 0 < m → 0 ≤ eosRatio k m ∧ eosRatio k m < 1 / 3) ∧
    (∀ k m ε : ℝ, 0 < m → 0 ≤ ε → |k| ≤ ε * m → eosRatio k m ≤ ε ^ 2 / 3) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k hk
    dsimp [eosRatio]
    have hk2 : k ^ 2 ≠ 0 := pow_ne_zero 2 hk
    rw [sq (0 : ℝ), mul_zero, add_zero, mul_comm 3 (k ^ 2), div_mul_eq_div_div,
        div_self hk2]
  · intro m; simp [eosRatio]
  · intro k m hm
    dsimp [eosRatio]
    have hm2 : 0 < m ^ 2 := sq_pos_of_pos hm
    have hk2 : 0 ≤ k ^ 2 := sq_nonneg k
    have hden : 0 < 3 * (k ^ 2 + m ^ 2) := by linarith
    refine ⟨div_nonneg hk2 (le_of_lt hden), ?_⟩
    rw [div_lt_iff₀ hden]
    linarith
  · intro k m ε hm hε hkm
    dsimp [eosRatio]
    have hm2 : 0 < m ^ 2 := sq_pos_of_pos hm
    have hk2 : 0 ≤ k ^ 2 := sq_nonneg k
    have hden : 0 < 3 * (k ^ 2 + m ^ 2) := by linarith
    have hk_le : k ^ 2 ≤ ε ^ 2 * m ^ 2 := by
      have h1 : |k| ^ 2 ≤ (ε * m) ^ 2 :=
        sq_le_sq.mpr (by rw [abs_abs, abs_of_nonneg (mul_nonneg hε (le_of_lt hm))]; exact hkm)
      simpa [sq_abs, mul_pow] using h1
    rw [div_le_iff₀ hden]
    have hnonneg : 0 ≤ ε ^ 2 * k ^ 2 := mul_nonneg (sq_nonneg ε) hk2
    linarith

end InfoGeometry.OperatorAlgebra.PeirceBiSandwich
