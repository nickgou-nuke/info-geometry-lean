/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Int.Order.Units
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Topology.Order.Filter
import Mathlib.Topology.Basic

noncomputable section

namespace InfoGeometry.OperatorAlgebra.NLinkElitzurChainAndCompactU1Gauge

open scoped BigOperators

/-! ### Section 0: Elementary Units ℤ Helpers -/

private lemma units_int_sq (u : Units ℤ) : u * u = 1 := by
  have hu := Int.units_eq_one_or u
  rcases hu with rfl | rfl
  · rfl
  · rfl

private lemma units_int_inv (u : Units ℤ) : u⁻¹ = u := by
  have hu := Int.units_eq_one_or u
  rcases hu with rfl | rfl
  · rfl
  · rfl

private lemma units_int_cast_sq (u : Units ℤ) : ((u : Int) : ℝ) ^ 2 = 1 := by
  have hu := Int.units_eq_one_or u
  rcases hu with rfl | rfl
  · norm_num
  · norm_num

private lemma units_int_cast_mul_self (u : Units ℤ) : ((u : Int) : ℝ) * ((u : Int) : ℝ) = 1 := by
  have hu := Int.units_eq_one_or u
  rcases hu with rfl | rfl
  · norm_num
  · norm_num

lemma units_int_sum (f : Units ℤ → ℝ) :
    ∑ u : Units ℤ, f u = f 1 + f (-1) := by
  have hu : (Finset.univ : Finset (Units ℤ)) = {1, -1} := by
    decide
  rw [hu]
  exact Finset.sum_pair (by decide)

/-! ### Section 1: N-Link Gauge-Higgs Chain Configuration & Action -/

abbrev ChainConfig (N : ℕ) := (Fin (N + 1) → Units ℤ) × (Fin N → Units ℤ)
abbrev GaugeGroup (N : ℕ) := Fin (N + 1) → Units ℤ

instance (N : ℕ) : Fintype (ChainConfig N) := by
  infer_instance

instance (N : ℕ) : Fintype (GaugeGroup N) := by
  infer_instance

def gaugeSmul (N : ℕ) (g : GaugeGroup N) (c : ChainConfig N) : ChainConfig N :=
  (fun i => g i * c.1 i, fun e => g e.castSucc * c.2 e * (g e.succ)⁻¹)

lemma gaugeSmul_one (N : ℕ) (c : ChainConfig N) : gaugeSmul N 1 c = c := by
  apply Prod.ext
  · ext i
    dsimp [gaugeSmul]
    generalize hu : c.1 i = u
    rcases Int.units_eq_one_or u with rfl | rfl <;> rfl
  · ext e
    dsimp [gaugeSmul]
    generalize hu : c.2 e = u
    rcases Int.units_eq_one_or u with rfl | rfl <;> rfl

lemma gaugeSmul_mul (N : ℕ) (g₁ g₂ : GaugeGroup N) (c : ChainConfig N) :
    gaugeSmul N (g₁ * g₂) c = gaugeSmul N g₁ (gaugeSmul N g₂ c) := by
  apply Prod.ext
  · ext i
    dsimp [gaugeSmul]
    rw [mul_assoc]
  · ext e
    dsimp [gaugeSmul]
    have h_u1 : (g₁ e.succ * g₂ e.succ)⁻¹ = (g₂ e.succ)⁻¹ * (g₁ e.succ)⁻¹ := mul_inv_rev (g₁ e.succ) (g₂ e.succ)
    rw [h_u1]
    generalize h1 : g₁ e.castSucc = u1
    generalize h2 : g₂ e.castSucc = u2
    generalize h3 : c.2 e = u3
    generalize h4 : (g₂ e.succ)⁻¹ = u4
    generalize h5 : (g₁ e.succ)⁻¹ = u5
    have hu1 := Int.units_eq_one_or u1
    have hu2 := Int.units_eq_one_or u2
    have hu3 := Int.units_eq_one_or u3
    have hu4 := Int.units_eq_one_or u4
    have hu5 := Int.units_eq_one_or u5
    rcases hu1 with rfl | rfl <;>
    rcases hu2 with rfl | rfl <;>
    rcases hu3 with rfl | rfl <;>
    rcases hu4 with rfl | rfl <;>
    rcases hu5 with rfl | rfl <;>
    decide

@[instance_reducible]
instance (N : ℕ) : MulAction (GaugeGroup N) (ChainConfig N) where
  smul := gaugeSmul N
  one_smul := gaugeSmul_one N
  mul_smul := gaugeSmul_mul N

@[instance_reducible]
def gaugeAction (N : ℕ) : MulAction (GaugeGroup N) (ChainConfig N) :=
  inferInstance

def tauLink {N : ℕ} (c : ChainConfig N) (e : Fin N) : Units ℤ :=
  c.1 e.castSucc * c.2 e * c.1 e.succ

theorem tauLink_gauge_invariant (N : ℕ) (g : GaugeGroup N) (c : ChainConfig N) (e : Fin N) :
    tauLink ((gaugeAction N).smul g c) e = tauLink c e := by
  change tauLink (gaugeSmul N g c) e = tauLink c e
  dsimp [tauLink, gaugeSmul]
  generalize hu1 : g e.castSucc = u1
  generalize hu2 : c.1 e.castSucc = u2
  generalize hu3 : c.2 e = u3
  generalize hu4 : g e.succ = u4
  generalize hu5 : c.1 e.succ = u5
  have h1 := Int.units_eq_one_or u1
  have h2 := Int.units_eq_one_or u2
  have h3 := Int.units_eq_one_or u3
  have h4 := Int.units_eq_one_or u4
  have h5 := Int.units_eq_one_or u5
  rcases h1 with rfl | rfl <;>
  rcases h2 with rfl | rfl <;>
  rcases h3 with rfl | rfl <;>
  rcases h4 with rfl | rfl <;>
  rcases h5 with rfl | rfl <;>
  decide

def H_chain (N : ℕ) (J : ℝ) (c : ChainConfig N) : ℝ :=
  J * ∑ e : Fin N, ((tauLink c e : Int) : ℝ)

def weightChain (N : ℕ) (J : ℝ) (c : ChainConfig N) : ℝ :=
  Real.exp (H_chain N J c)

def Z_chain (N : ℕ) (J : ℝ) : ℝ :=
  ∑ c : ChainConfig N, weightChain N J c

theorem weightChain_pos (N : ℕ) (J : ℝ) (c : ChainConfig N) :
    0 < weightChain N J c := by
  dsimp [weightChain]
  exact Real.exp_pos _

theorem Z_chain_pos (N : ℕ) (J : ℝ) :
    0 < Z_chain N J := by
  dsimp [Z_chain]
  have hnonempty : Nonempty (ChainConfig N) := by
    infer_instance
  obtain ⟨c0⟩ := hnonempty
  have hpos : 0 < weightChain N J c0 := weightChain_pos N J c0
  have hle : weightChain N J c0 ≤ ∑ c : ChainConfig N, weightChain N J c := by
    apply Finset.single_le_sum
    · intro c _
      exact le_of_lt (weightChain_pos N J c)
    · exact Finset.mem_univ c0
  linarith

theorem Z_chain_ne_zero (N : ℕ) (J : ℝ) :
    Z_chain N J ≠ 0 := by
  exact ne_of_gt (Z_chain_pos N J)

def expectChain (N : ℕ) (J : ℝ) (O : ChainConfig N → ℝ) : ℝ :=
  (∑ c : ChainConfig N, O c * weightChain N J c) / Z_chain N J

/-! ### Section 2: Exact Local Gauge Expectation Vanishing (Elitzur's Theorem) -/

def flipAt (x : Fin (N + 1)) : GaugeGroup N :=
  fun i => if i = x then -1 else 1

lemma flipAt_mul_self (x : Fin (N + 1)) : flipAt x * flipAt x = 1 := by
  ext i
  dsimp [flipAt]
  split_ifs <;> rfl

def flipEquiv (x : Fin (N + 1)) : ChainConfig N ≃ ChainConfig N where
  toFun c := (gaugeAction N).smul (flipAt x) c
  invFun c := (gaugeAction N).smul (flipAt x) c
  left_inv c := by
    change gaugeSmul N (flipAt x) (gaugeSmul N (flipAt x) c) = c
    rw [← gaugeSmul_mul, flipAt_mul_self, gaugeSmul_one]
  right_inv c := by
    change gaugeSmul N (flipAt x) (gaugeSmul N (flipAt x) c) = c
    rw [← gaugeSmul_mul, flipAt_mul_self, gaugeSmul_one]

lemma weightChain_flipEquiv (N : ℕ) (J : ℝ) (x : Fin (N + 1)) (c : ChainConfig N) :
    weightChain N J (flipEquiv x c) = weightChain N J c := by
  dsimp [weightChain, H_chain]
  congr 2
  apply Finset.sum_congr rfl
  intro e _
  have htau : tauLink (flipEquiv x c) e = tauLink c e := by
    exact tauLink_gauge_invariant N (flipAt x) c e
  rw [htau]

lemma flipEquiv_apply_self (x : Fin (N + 1)) (c : ChainConfig N) :
    (((flipEquiv x c).1 x : Int) : ℝ) = - (((c.1 x : Int) : ℝ)) := by
  change (((gaugeSmul N (flipAt x) c).1 x : Int) : ℝ) = - (((c.1 x : Int) : ℝ))
  dsimp [gaugeSmul]
  have hx : flipAt x x = -1 := by
    dsimp [flipAt]
    split_ifs with h
    · rfl
    · contradiction
  rw [hx]
  generalize hu : c.1 x = u
  rcases Int.units_eq_one_or u with rfl | rfl <;> norm_num

lemma flipEquiv_apply_ne {x y : Fin (N + 1)} (h : y ≠ x) (c : ChainConfig N) :
    (((flipEquiv x c).1 y : Int) : ℝ) = (((c.1 y : Int) : ℝ)) := by
  change (((gaugeSmul N (flipAt x) c).1 y : Int) : ℝ) = (((c.1 y : Int) : ℝ))
  dsimp [gaugeSmul]
  have hy : flipAt x y = 1 := by
    dsimp [flipAt]
    split_ifs with heq
    · exact False.elim (h heq)
    · rfl
  rw [hy]
  generalize hu : c.1 y = u
  rcases Int.units_eq_one_or u with rfl | rfl <;> norm_num

theorem expectChain_sigma_zero (N : ℕ) (J : ℝ) (x : Fin (N + 1)) :
    expectChain N J (fun c => ((c.1 x : Int) : ℝ)) = 0 := by
  dsimp [expectChain]
  have hsum : ∑ c : ChainConfig N, ((c.1 x : Int) : ℝ) * weightChain N J c = 0 := by
    have hcomp : ∑ c : ChainConfig N, ((c.1 x : Int) : ℝ) * weightChain N J c =
        ∑ c : ChainConfig N, (((flipEquiv x c).1 x : Int) : ℝ) * weightChain N J (flipEquiv x c) := by
      exact (Equiv.sum_comp (flipEquiv x) _).symm
    have hneg : ∑ c : ChainConfig N, (((flipEquiv x c).1 x : Int) : ℝ) * weightChain N J (flipEquiv x c) =
        - ∑ c : ChainConfig N, ((c.1 x : Int) : ℝ) * weightChain N J c := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro c _
      rw [flipEquiv_apply_self, weightChain_flipEquiv]
      ring
    linarith
  rw [hsum, zero_div]

theorem expectChain_sigma_pair_zero (N : ℕ) (J : ℝ) {x y : Fin (N + 1)} (hxy : x ≠ y) :
    expectChain N J (fun c => ((c.1 x : Int) : ℝ) * ((c.1 y : Int) : ℝ)) = 0 := by
  dsimp [expectChain]
  have hsum : ∑ c : ChainConfig N, (((c.1 x : Int) : ℝ) * ((c.1 y : Int) : ℝ)) * weightChain N J c = 0 := by
    have hcomp : ∑ c : ChainConfig N, (((c.1 x : Int) : ℝ) * ((c.1 y : Int) : ℝ)) * weightChain N J c =
        ∑ c : ChainConfig N, ((((flipEquiv x c).1 x : Int) : ℝ) * (((flipEquiv x c).1 y : Int) : ℝ)) *
          weightChain N J (flipEquiv x c) := by
      exact (Equiv.sum_comp (flipEquiv x) _).symm
    have hneg : ∑ c : ChainConfig N, ((((flipEquiv x c).1 x : Int) : ℝ) * (((flipEquiv x c).1 y : Int) : ℝ)) *
          weightChain N J (flipEquiv x c) =
        - ∑ c : ChainConfig N, (((c.1 x : Int) : ℝ) * ((c.1 y : Int) : ℝ)) * weightChain N J c := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro c _
      rw [flipEquiv_apply_self, flipEquiv_apply_ne (Ne.symm hxy), weightChain_flipEquiv]
      ring
    linarith
  rw [hsum, zero_div]

/-! ### Section 3: Closed-Form Wilson String & Exponential Mass-Gap Decay -/

def wilsonString (N : ℕ) (L : ℕ) (hL : L ≤ N) (c : ChainConfig N) : ℝ :=
  ((c.1 0 : Int) : ℝ) * (∏ k : Fin L, ((c.2 (k.castLE hL) : Int) : ℝ)) * ((c.1 ⟨L, by omega⟩ : Int) : ℝ)

def linkEquiv (N : ℕ) (s : Fin (N + 1) → Units ℤ) : (Fin N → Units ℤ) ≃ (Fin N → Units ℤ) where
  toFun u e := s e.castSucc * u e * s e.succ
  invFun τ e := s e.castSucc * τ e * s e.succ
  left_inv u := by
    ext e
    dsimp
    generalize h1 : s e.castSucc = s1
    generalize h2 : u e = u0
    generalize h3 : s e.succ = s2
    have hu1 := Int.units_eq_one_or s1
    have hu2 := Int.units_eq_one_or u0
    have hu3 := Int.units_eq_one_or s2
    rcases hu1 with rfl | rfl <;>
    rcases hu2 with rfl | rfl <;>
    rcases hu3 with rfl | rfl <;>
    decide
  right_inv τ := by
    ext e
    dsimp
    generalize h1 : s e.castSucc = s1
    generalize h2 : τ e = τ0
    generalize h3 : s e.succ = s2
    have hu1 := Int.units_eq_one_or s1
    have hu2 := Int.units_eq_one_or τ0
    have hu3 := Int.units_eq_one_or s2
    rcases hu1 with rfl | rfl <;>
    rcases hu2 with rfl | rfl <;>
    rcases hu3 with rfl | rfl <;>
    decide

def tauTransform (N : ℕ) : ChainConfig N ≃ ChainConfig N where
  toFun c := (c.1, linkEquiv N c.1 c.2)
  invFun c := (c.1, (linkEquiv N c.1).symm c.2)
  left_inv c := by
    apply Prod.ext
    · rfl
    · dsimp
      exact (linkEquiv N c.1).left_inv c.2
  right_inv c := by
    apply Prod.ext
    · rfl
    · dsimp
      exact (linkEquiv N c.1).right_inv c.2

lemma tauLink_eq_tauTransform_snd (N : ℕ) (c : ChainConfig N) (e : Fin N) :
    tauLink ((tauTransform N).symm c) e = c.2 e := by
  change tauLink (c.1, (linkEquiv N c.1).symm c.2) e = c.2 e
  dsimp [tauLink, linkEquiv]
  generalize h1 : c.1 e.castSucc = s1
  generalize h2 : c.2 e = τ0
  generalize h3 : c.1 e.succ = s2
  have hu1 := Int.units_eq_one_or s1
  have hu2 := Int.units_eq_one_or τ0
  have hu3 := Int.units_eq_one_or s2
  rcases hu1 with rfl | rfl <;>
  rcases hu2 with rfl | rfl <;>
  rcases hu3 with rfl | rfl <;>
  decide

theorem wilsonString_eq_prod_tau (N L : ℕ) (hL : L ≤ N) (c : ChainConfig N) :
    wilsonString N L hL c = ∏ k : Fin L, ((tauLink c (k.castLE hL) : Int) : ℝ) := by
  induction L with
  | zero =>
    dsimp [wilsonString]
    rw [Fin.prod_univ_zero, mul_one, units_int_cast_mul_self, Fin.prod_univ_zero]
  | succ L ih =>
    have hL_prev : L ≤ N := by omega
    have h_prod_tau : (∏ k : Fin (L + 1), ((tauLink c (k.castLE hL) : Int) : ℝ)) =
        (∏ k : Fin L, ((tauLink c (k.castLE hL_prev) : Int) : ℝ)) *
          ((tauLink c ⟨L, by omega⟩ : Int) : ℝ) := by
      rw [Fin.prod_univ_castSucc]
      have h1 : (Fin.last L).castLE hL = (⟨L, by omega⟩ : Fin N) := by
        ext
        rfl
      rw [h1]
      have h2 : (fun (k : Fin L) => ((tauLink c (k.castSucc.castLE hL) : Int) : ℝ)) =
          (fun k => ((tauLink c (k.castLE hL_prev) : Int) : ℝ)) := by
        funext k
        have hk : k.castSucc.castLE hL = k.castLE hL_prev := by
          ext
          rfl
        rw [hk]
      rw [h2]
    have h_prod_c2 : (∏ k : Fin (L + 1), ((c.2 (k.castLE hL) : Int) : ℝ)) =
        (∏ k : Fin L, ((c.2 (k.castLE hL_prev) : Int) : ℝ)) *
          ((c.2 ⟨L, by omega⟩ : Int) : ℝ) := by
      rw [Fin.prod_univ_castSucc]
      have h1 : (Fin.last L).castLE hL = (⟨L, by omega⟩ : Fin N) := by
        ext
        rfl
      rw [h1]
      have h2 : (fun (k : Fin L) => ((c.2 (k.castSucc.castLE hL) : Int) : ℝ)) =
          (fun k => ((c.2 (k.castLE hL_prev) : Int) : ℝ)) := by
        funext k
        have hk : k.castSucc.castLE hL = k.castLE hL_prev := by
          ext
          rfl
        rw [hk]
      rw [h2]
    rw [h_prod_tau, ← ih hL_prev]
    dsimp [wilsonString]
    rw [h_prod_c2]
    have h_tau_expand : ((tauLink c ⟨L, by omega⟩ : Int) : ℝ) =
        ((c.1 ⟨L, by omega⟩ : Int) : ℝ) * ((c.2 ⟨L, by omega⟩ : Int) : ℝ) *
          ((c.1 ⟨L + 1, by omega⟩ : Int) : ℝ) := by
      dsimp [tauLink]
      push_cast
      rfl
    rw [h_tau_expand]
    have hsq := units_int_cast_mul_self (c.1 ⟨L, by omega⟩)
    rw [← mul_assoc ((c.1 0 : Int) : ℝ)]
    set A := ((c.1 0 : Int) : ℝ) * ∏ k : Fin L, ((c.2 (k.castLE hL_prev) : Int) : ℝ)
    set B := ((c.1 ⟨L, by omega⟩ : Int) : ℝ)
    set C := ((c.2 ⟨L, by omega⟩ : Int) : ℝ)
    set D := ((c.1 ⟨L + 1, by omega⟩ : Int) : ℝ)
    calc A * C * D
      _ = A * 1 * C * D := by rw [mul_one]
      _ = A * (B * B) * C * D := by rw [← hsq]
      _ = (A * B) * (B * C * D) := by ring

lemma sum_chain_decouple (N : ℕ) (J : ℝ) (F : (Fin N → Units ℤ) → ℝ) :
    ∑ c : ChainConfig N, F (tauLink c) * weightChain N J c =
      (Fintype.card (Fin (N + 1) → Units ℤ) : ℝ) *
        ∑ τ : Fin N → Units ℤ, F τ * Real.exp (J * ∑ e : Fin N, ((τ e : Int) : ℝ)) := by
  have h1 : ∑ c : ChainConfig N, F (tauLink c) * weightChain N J c =
      ∑ c : ChainConfig N, F (tauLink ((tauTransform N).symm c)) * weightChain N J ((tauTransform N).symm c) := by
    exact (Equiv.sum_comp (tauTransform N).symm _).symm
  rw [h1]
  have h_tau : (fun c : ChainConfig N => F (tauLink ((tauTransform N).symm c)) * weightChain N J ((tauTransform N).symm c)) =
      (fun c : ChainConfig N => F c.2 * Real.exp (J * ∑ e : Fin N, ((c.2 e : Int) : ℝ))) := by
    funext c
    have htau_eq : tauLink ((tauTransform N).symm c) = c.2 := by
      funext e
      exact tauLink_eq_tauTransform_snd N c e
    rw [htau_eq]
    dsimp [weightChain, H_chain]
    have h_sum : (∑ e : Fin N, ((tauLink ((tauTransform N).symm c) e : Int) : ℝ)) =
        (∑ e : Fin N, ((c.2 e : Int) : ℝ)) := by
      apply Finset.sum_congr rfl
      intro e _
      congr 1
      congr 1
      exact tauLink_eq_tauTransform_snd N c e
    rw [h_sum]
  rw [h_tau]
  rw [Fintype.sum_prod_type]
  dsimp
  rw [Finset.sum_const]
  simp only [Finset.card_univ, nsmul_eq_mul]

lemma filter_lt_eq_image (N L : ℕ) (hL : L ≤ N) :
    Finset.filter (fun e : Fin N => e.val < L) Finset.univ =
      Finset.image (fun k : Fin L => k.castLE hL) Finset.univ := by
  ext e
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · intro he
    exact ⟨⟨e.val, he⟩, by ext; rfl⟩
  · rintro ⟨k, rfl⟩
    exact k.is_lt

lemma prod_filter_castLE (N L : ℕ) (hL : L ≤ N) (f : Fin N → ℝ) :
    (∏ e ∈ Finset.filter (fun e : Fin N => e.val < L) Finset.univ, f e) = ∏ k : Fin L, f (k.castLE hL) := by
  rw [filter_lt_eq_image N L hL]
  have hinj : Set.InjOn (fun k : Fin L => k.castLE hL) (Finset.univ : Finset (Fin L)) := by
    intro a _ b _ hab
    exact Fin.ext (by simpa using congrArg Fin.val hab)
  exact Finset.prod_image hinj

lemma card_filter_lt (N L : ℕ) (hL : L ≤ N) :
    (Finset.filter (fun e : Fin N => e.val < L) Finset.univ).card = L := by
  rw [filter_lt_eq_image N L hL]
  have hinj : Set.InjOn (fun k : Fin L => k.castLE hL) (Finset.univ : Finset (Fin L)) := by
    intro a _ b _ hab
    exact Fin.ext (by simpa using congrArg Fin.val hab)
  rw [Finset.card_image_of_injOn hinj, Finset.card_univ, Fintype.card_fin]

lemma card_filter_ge (N L : ℕ) (hL : L ≤ N) :
    (Finset.filter (fun e : Fin N => ¬ (e.val < L)) Finset.univ).card = N - L := by
  have hcard := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin N)))
    (p := fun e : Fin N => e.val < L)
  rw [Finset.card_univ, Fintype.card_fin, card_filter_lt N L hL] at hcard
  omega

lemma real_two_cosh (x : ℝ) : 2 * Real.cosh x = Real.exp x + Real.exp (-x) := by
  apply Complex.ofReal_injective
  push_cast
  exact Complex.two_cosh (x : ℂ)

lemma real_two_sinh (x : ℝ) : 2 * Real.sinh x = Real.exp x - Real.exp (-x) := by
  apply Complex.ofReal_injective
  push_cast
  exact Complex.two_sinh (x : ℂ)

lemma sum_exp_links (N : ℕ) (J : ℝ) :
    (∑ τ : Fin N → Units ℤ, Real.exp (J * ∑ e : Fin N, ((τ e : Int) : ℝ))) =
      (2 * Real.cosh J) ^ N := by
  have h_exp : (fun τ : Fin N → Units ℤ => Real.exp (J * ∑ e : Fin N, ((τ e : Int) : ℝ))) =
      (fun τ => ∏ e : Fin N, Real.exp (J * ((τ e : Int) : ℝ))) := by
    funext τ
    rw [Finset.mul_sum, Real.exp_sum]
  rw [h_exp]
  have h_factor := (Fintype.prod_sum (fun (e : Fin N) (u : Units ℤ) => Real.exp (J * ((u : Int) : ℝ)))).symm
  rw [h_factor]
  have hu : ∀ e : Fin N, (∑ u : Units ℤ, Real.exp (J * ((u : Int) : ℝ))) = 2 * Real.cosh J := by
    intro e
    rw [units_int_sum]
    have h1 : (((1 : Units ℤ) : Int) : ℝ) = 1 := by norm_num
    have h2 : (((-1 : Units ℤ) : Int) : ℝ) = -1 := by norm_num
    rw [h1, h2]
    rw [mul_one, mul_neg, mul_one]
    rw [real_two_cosh]
  have h_prod : (∏ e : Fin N, ∑ u : Units ℤ, Real.exp (J * ((u : Int) : ℝ))) =
      ∏ e : Fin N, (2 * Real.cosh J) := by
    apply Finset.prod_congr rfl
    intro e _
    exact hu e
  rw [h_prod, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

def linkTerm (L : ℕ) (J : ℝ) (e : Fin N) (u : Units ℤ) : ℝ :=
  (if e.val < L then ((u : Int) : ℝ) else 1) * Real.exp (J * ((u : Int) : ℝ))

lemma sum_wilson_tau (N L : ℕ) (hL : L ≤ N) (J : ℝ) :
    (∑ τ : Fin N → Units ℤ, (∏ k : Fin L, ((τ (k.castLE hL) : Int) : ℝ)) * Real.exp (J * ∑ e : Fin N, ((τ e : Int) : ℝ))) =
      (2 * Real.sinh J) ^ L * (2 * Real.cosh J) ^ (N - L) := by
  have h_prod_tau : ∀ τ : Fin N → Units ℤ,
      (∏ k : Fin L, ((τ (k.castLE hL) : Int) : ℝ)) * Real.exp (J * ∑ e : Fin N, ((τ e : Int) : ℝ)) =
        ∏ e : Fin N, linkTerm L J e (τ e) := by
    intro τ
    dsimp [linkTerm]
    rw [Finset.prod_mul_distrib]
    have h_exp : (∏ e : Fin N, Real.exp (J * ((τ e : Int) : ℝ))) = Real.exp (J * ∑ e : Fin N, ((τ e : Int) : ℝ)) := by
      rw [← Real.exp_sum, ← Finset.mul_sum]
    rw [h_exp]
    congr 1
    have h_split := Finset.prod_filter_mul_prod_filter_not (s := (Finset.univ : Finset (Fin N)))
      (p := fun e : Fin N => e.val < L) (f := fun e : Fin N => if e.val < L then ((τ e : Int) : ℝ) else 1)
    rw [← h_split]
    have h_lt : (∏ e ∈ Finset.filter (fun e : Fin N => e.val < L) Finset.univ,
        (if e.val < L then ((τ e : Int) : ℝ) else 1)) =
          ∏ e ∈ Finset.filter (fun e : Fin N => e.val < L) Finset.univ, ((τ e : Int) : ℝ) := by
      apply Finset.prod_congr rfl
      intro e he
      rw [Finset.mem_filter] at he
      simp [he.2]
    have h_ge : (∏ e ∈ Finset.filter (fun e : Fin N => ¬ (e.val < L)) Finset.univ,
        (if e.val < L then ((τ e : Int) : ℝ) else 1)) = 1 := by
      rw [Finset.prod_eq_one]
      intro e he
      rw [Finset.mem_filter] at he
      simp [he.2]
    rw [h_lt, h_ge, mul_one, prod_filter_castLE N L hL]
  have h_sum_tau : (∑ τ : Fin N → Units ℤ, (∏ k : Fin L, ((τ (k.castLE hL) : Int) : ℝ)) *
      Real.exp (J * ∑ e : Fin N, ((τ e : Int) : ℝ))) =
        ∑ τ : Fin N → Units ℤ, ∏ e : Fin N, linkTerm L J e (τ e) := by
    apply Finset.sum_congr rfl
    intro τ _
    exact h_prod_tau τ
  rw [h_sum_tau]
  rw [← Fintype.prod_sum]
  have hu : ∀ e : Fin N, (∑ u : Units ℤ, linkTerm L J e u) =
      if e.val < L then 2 * Real.sinh J else 2 * Real.cosh J := by
    intro e
    rw [units_int_sum]
    dsimp [linkTerm]
    norm_num
    split_ifs with he
    · rw [real_two_sinh]
      ring
    · rw [real_two_cosh]
  have h_prod_e : (∏ e : Fin N, ∑ u : Units ℤ, linkTerm L J e u) =
      (2 * Real.sinh J) ^ L * (2 * Real.cosh J) ^ (N - L) := by
    have h_eq : (∏ e : Fin N, ∑ u : Units ℤ, linkTerm L J e u) =
        ∏ e : Fin N, if e.val < L then 2 * Real.sinh J else 2 * Real.cosh J := by
      apply Finset.prod_congr rfl
      intro e _
      exact hu e
    rw [h_eq]
    have h_split := Finset.prod_filter_mul_prod_filter_not (s := (Finset.univ : Finset (Fin N)))
      (p := fun e : Fin N => e.val < L) (f := fun e : Fin N => if e.val < L then 2 * Real.sinh J else 2 * Real.cosh J)
    rw [← h_split]
    have h_lt : (∏ e ∈ Finset.filter (fun e : Fin N => e.val < L) Finset.univ,
        (if e.val < L then 2 * Real.sinh J else 2 * Real.cosh J)) =
          (2 * Real.sinh J) ^ L := by
      have h1 : (∏ e ∈ Finset.filter (fun e : Fin N => e.val < L) Finset.univ,
          (if e.val < L then 2 * Real.sinh J else 2 * Real.cosh J)) =
            ∏ e ∈ Finset.filter (fun e : Fin N => e.val < L) Finset.univ, (2 * Real.sinh J) := by
        apply Finset.prod_congr rfl
        intro e he
        rw [Finset.mem_filter] at he
        simp [he.2]
      rw [h1, Finset.prod_const, card_filter_lt N L hL]
    have h_ge : (∏ e ∈ Finset.filter (fun e : Fin N => ¬ (e.val < L)) Finset.univ,
        (if e.val < L then 2 * Real.sinh J else 2 * Real.cosh J)) =
          (2 * Real.cosh J) ^ (N - L) := by
      have h1 : (∏ e ∈ Finset.filter (fun e : Fin N => ¬ (e.val < L)) Finset.univ,
          (if e.val < L then 2 * Real.sinh J else 2 * Real.cosh J)) =
            ∏ e ∈ Finset.filter (fun e : Fin N => ¬ (e.val < L)) Finset.univ, (2 * Real.cosh J) := by
        apply Finset.prod_congr rfl
        intro e he
        rw [Finset.mem_filter] at he
        simp [he.2]
      rw [h1, Finset.prod_const, card_filter_ge N L hL]
    rw [h_lt, h_ge]
  exact h_prod_e

theorem expectChain_wilson_eq_tanh_pow (N L : ℕ) (hL : L ≤ N) (J : ℝ) :
    expectChain N J (wilsonString N L hL) = (Real.tanh J) ^ L := by
  dsimp [expectChain, Z_chain]
  have h_num : (∑ c : ChainConfig N, wilsonString N L hL c * weightChain N J c) =
      (Fintype.card (Fin (N + 1) → Units ℤ) : ℝ) * ((2 * Real.sinh J) ^ L * (2 * Real.cosh J) ^ (N - L)) := by
    have h1 : (∑ c : ChainConfig N, wilsonString N L hL c * weightChain N J c) =
        ∑ c : ChainConfig N, (∏ k : Fin L, ((tauLink c (k.castLE hL) : Int) : ℝ)) * weightChain N J c := by
      apply Finset.sum_congr rfl
      intro c _
      rw [wilsonString_eq_prod_tau N L hL c]
    rw [h1]
    rw [sum_chain_decouple N J (fun τ => ∏ k : Fin L, ((τ (k.castLE hL) : Int) : ℝ))]
    rw [sum_wilson_tau N L hL J]
  have h_den : (∑ c : ChainConfig N, weightChain N J c) =
      (Fintype.card (Fin (N + 1) → Units ℤ) : ℝ) * (2 * Real.cosh J) ^ N := by
    have h1 : (∑ c : ChainConfig N, weightChain N J c) =
        ∑ c : ChainConfig N, (1 : ℝ) * weightChain N J c := by
      simp only [one_mul]
    rw [h1]
    rw [sum_chain_decouple N J (fun _ => 1)]
    have h_sum_links : (∑ τ : Fin N → Units ℤ, (1 : ℝ) * Real.exp (J * ∑ e : Fin N, ((τ e : Int) : ℝ))) =
        (2 * Real.cosh J) ^ N := by
      simp only [one_mul]
      exact sum_exp_links N J
    rw [h_sum_links]
  rw [h_num, h_den]
  have h_card_ne : (Fintype.card (Fin (N + 1) → Units ℤ) : ℝ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have h_cosh_pos : 0 < 2 * Real.cosh J := by
    have : 0 < Real.cosh J := Real.cosh_pos J
    linarith
  have h_cosh_pow_ne : (2 * Real.cosh J) ^ (N - L) ≠ 0 := by
    exact ne_of_gt (pow_pos h_cosh_pos (N - L))
  have h_cosh_pow_L_ne : (2 * Real.cosh J) ^ L ≠ 0 := by
    exact ne_of_gt (pow_pos h_cosh_pos L)
  have h_pow_split : (2 * Real.cosh J) ^ N = (2 * Real.cosh J) ^ L * (2 * Real.cosh J) ^ (N - L) := by
    have h_add : N = L + (N - L) := by omega
    nth_rewrite 1 [h_add]
    rw [pow_add]
  rw [h_pow_split]
  have h_cancel1 : ((Fintype.card (Fin (N + 1) → Units ℤ) : ℝ) * ((2 * Real.sinh J) ^ L * (2 * Real.cosh J) ^ (N - L))) /
      ((Fintype.card (Fin (N + 1) → Units ℤ) : ℝ) * ((2 * Real.cosh J) ^ L * (2 * Real.cosh J) ^ (N - L))) =
        ((2 * Real.sinh J) ^ L * (2 * Real.cosh J) ^ (N - L)) /
          ((2 * Real.cosh J) ^ L * (2 * Real.cosh J) ^ (N - L)) := by
    rw [mul_div_mul_left _ _ h_card_ne]
  rw [h_cancel1]
  have h_cancel2 : ((2 * Real.sinh J) ^ L * (2 * Real.cosh J) ^ (N - L)) /
      ((2 * Real.cosh J) ^ L * (2 * Real.cosh J) ^ (N - L)) =
        (2 * Real.sinh J) ^ L / (2 * Real.cosh J) ^ L := by
    rw [mul_div_mul_right _ _ h_cosh_pow_ne]
  rw [h_cancel2]
  rw [← div_pow]
  have h_ratio : (2 * Real.sinh J) / (2 * Real.cosh J) = Real.tanh J := by
    rw [mul_div_mul_left (Real.sinh J) (Real.cosh J) two_ne_zero]
    exact (Real.tanh_eq_sinh_div_cosh J).symm
  rw [h_ratio]

theorem expectChain_wilson_pos (N L : ℕ) (hL : L ≤ N) {J : ℝ} (hJ : 0 < J) :
    0 < expectChain N J (wilsonString N L hL) := by
  rw [expectChain_wilson_eq_tanh_pow N L hL J]
  have ht : 0 < Real.tanh J := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr hJ) (Real.cosh_pos J)
  exact pow_pos ht L

theorem expectChain_wilson_tendsto_zero {J : ℝ} (hJ : 0 < J) :
    Filter.Tendsto (fun L : ℕ => (Real.tanh J) ^ L) Filter.atTop (nhds 0) := by
  have ht_nonneg : 0 ≤ Real.tanh J := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact le_of_lt (div_pos (Real.sinh_pos_iff.mpr hJ) (Real.cosh_pos J))
  exact tendsto_pow_atTop_nhds_zero_of_lt_one ht_nonneg (Real.tanh_lt_one J)

/-! ### Section 4: Continuous Compact U(1) Haar Integral Elitzur Vanishing -/

def u1HaarAvg (f : ℝ → ℂ) : ℂ :=
  (1 / (2 * Real.pi)) • ∫ θ in (0 : ℝ)..(2 * Real.pi), f θ

theorem u1HaarAvg_one : u1HaarAvg (fun _ => 1) = 1 := by
  dsimp [u1HaarAvg]
  have h_int : (∫ _ in (0 : ℝ)..(2 * Real.pi), (1 : ℂ)) = (2 * Real.pi : ℝ) • (1 : ℂ) := by
    rw [intervalIntegral.integral_const (1 : ℂ)]
    simp only [sub_zero]
  rw [h_int]
  dsimp [HSMul.hSMul, SMul.smul]
  push_cast
  have h_pi : (2 : ℂ) * (Real.pi : ℂ) ≠ 0 := by
    apply mul_ne_zero two_ne_zero
    exact_mod_cast Real.pi_ne_zero
  rw [mul_one]
  exact div_mul_cancel₀ 1 h_pi

theorem u1HaarAvg_translation_invariant (f : ℝ → ℂ) (hper : Function.Periodic f (2 * Real.pi)) (α : ℝ) :
    u1HaarAvg (fun θ => f (θ + α)) = u1HaarAvg f := by
  dsimp [u1HaarAvg]
  congr 1
  rw [intervalIntegral.integral_comp_add_right (f := f) (d := α)]
  have h_add : 2 * Real.pi + α = α + 2 * Real.pi := by ring
  rw [zero_add, h_add]
  have h_per := hper.intervalIntegral_add_eq α 0
  rw [zero_add] at h_per
  exact h_per

theorem u1HaarAvg_charge_vanishing (q : ℤ) (hq : q ≠ 0) :
    u1HaarAvg (fun θ => Complex.exp (Complex.I * (q : ℂ) * θ)) = 0 := by
  dsimp [u1HaarAvg]
  have hc : Complex.I * (q : ℂ) ≠ 0 := by
    apply mul_ne_zero Complex.I_ne_zero
    exact_mod_cast hq
  have h_int : (∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (Complex.I * (q : ℂ) * θ)) = 0 := by
    rw [integral_exp_mul_complex hc]
    have h_top : Complex.exp (Complex.I * (q : ℂ) * ((2 * Real.pi : ℝ) : ℂ)) = 1 := by
      have heq : Complex.I * (q : ℂ) * ((2 * Real.pi : ℝ) : ℂ) = (q : ℂ) * (2 * Real.pi * Complex.I) := by
        push_cast
        ring
      rw [heq]
      exact Complex.exp_int_mul_two_pi_mul_I q
    have h_bot : Complex.exp (Complex.I * (q : ℂ) * ((0 : ℝ) : ℂ)) = 1 := by
      have heq : Complex.I * (q : ℂ) * ((0 : ℝ) : ℂ) = 0 := by
        push_cast
        ring
      rw [heq, Complex.exp_zero]
    rw [h_top, h_bot, sub_self, zero_div]
  rw [h_int]
  exact mul_zero _

/-! ### Section 5: OpenGauss T16 Matrix Non-Commutativity Witness -/

def matX : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]
def matZ : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]

theorem lattice_gauge_algebra_noncommuting : matX * matZ ≠ matZ * matX := by
  intro h
  have hh := congrArg (fun a : Matrix (Fin 2) (Fin 2) ℝ => a 0 1) h
  norm_num [matX, matZ, Matrix.mul_apply, Fin.sum_univ_two] at hh

end InfoGeometry.OperatorAlgebra.NLinkElitzurChainAndCompactU1Gauge
