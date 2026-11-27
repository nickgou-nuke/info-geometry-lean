/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.UnboundedHilbertResolventAndC0GroupWitness
import InfoGeometry.OperatorAlgebra.C0GroupGenerator
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Strong continuity and exact generator domain of the real block-rotation flow

The carrier and operators are the actual `H_lp`, `U_unb`, `D_max` and `K_max`
of `UnboundedHilbertResolventAndC0GroupWitness`. Coordinate convergence is
upgraded to convergence in the Hilbert norm using a summable square bound.
No operator-norm continuity is asserted: `K_max` is unbounded.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.UnboundedHilbertResolventAndC0GroupWitness

open Filter
open scoped Topology

/-- A dominated convergence criterion in the actual real `ℓ²` norm. -/
theorem tendsto_lp_of_coordinatewise_sq_bound {α : Type*} {l : Filter α}
    {f : α → H_lp} {y : H_lp} {b : ℕ → ℝ} (hb : Summable b)
    (hcoord : ∀ n, Tendsto (fun a => f a n) l (𝓝 (y n)))
    (hbound : ∀ᶠ a in l, ∀ n, (f a n - y n) ^ 2 ≤ b n) :
    Tendsto f l (𝓝 y) := by
  have hsq : Tendsto (fun a => ∑' n, (f a n - y n) ^ 2) l (𝓝 0) := by
    have h := tendsto_tsum_of_dominated_convergence hb
      (f := fun a n => (f a n - y n) ^ 2)
      (g := fun _ : ℕ => (0 : ℝ))
      (fun n => by
        have hc : Tendsto (fun _ : α => y n) l (𝓝 (y n)) := tendsto_const_nhds
        simpa using ((hcoord n).sub hc).pow 2)
      (hbound.mono fun a ha n => by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (f a n - y n))] using ha n)
    simpa using h
  have hnormsq : Tendsto (fun a => ‖f a - y‖ ^ 2) l (𝓝 0) := by
    simpa only [norm_sq_eq_tsum, lp.coeFn_sub, Pi.sub_apply] using hsq
  have hnorm := Real.continuous_sqrt.continuousAt.tendsto.comp hnormsq
  exact tendsto_iff_norm_sub_tendsto_zero.mpr
    (by simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hnorm)

/-- The sum of the squares in the coordinate pair containing `n`. -/
def pairSquareSum (x : H_lp) (n : ℕ) : ℝ :=
  (x (2 * (n / 2))) ^ 2 + (x (2 * (n / 2) + 1)) ^ 2

@[simp] theorem pairSquareSum_even (x : H_lp) (m : ℕ) :
    pairSquareSum x (2 * m) = (x (2 * m)) ^ 2 + (x (2 * m + 1)) ^ 2 := by
  have h : (2 * m) / 2 = m := by omega
  simp [pairSquareSum, h]

@[simp] theorem pairSquareSum_odd (x : H_lp) (m : ℕ) :
    pairSquareSum x (2 * m + 1) = (x (2 * m)) ^ 2 + (x (2 * m + 1)) ^ 2 := by
  have h : (2 * m + 1) / 2 = m := by omega
  simp [pairSquareSum, h]

theorem pairSquareSum_nonneg (x : H_lp) (n : ℕ) : 0 ≤ pairSquareSum x n := by
  unfold pairSquareSum
  positivity

theorem coord_sq_le_pairSquareSum (x : H_lp) (n : ℕ) :
    (x n) ^ 2 ≤ pairSquareSum x n := by
  unfold pairSquareSum
  by_cases h : n % 2 = 0
  · have hn : n = 2 * (n / 2) := by omega
    calc
      (x n) ^ 2 = (x (2 * (n / 2))) ^ 2 := congrArg (fun k => (x k) ^ 2) hn
      _ ≤ _ := le_add_of_nonneg_right (sq_nonneg (x (2 * (n / 2) + 1)))
  · have hn : n = 2 * (n / 2) + 1 := by omega
    calc
      (x n) ^ 2 = (x (2 * (n / 2) + 1)) ^ 2 := congrArg (fun k => (x k) ^ 2) hn
      _ ≤ _ := le_add_of_nonneg_left (sq_nonneg (x (2 * (n / 2))))

theorem summable_pairSquareSum (x : H_lp) : Summable (pairSquareSum x) := by
  refine summable_of_sum_range_le (c := 2 * ∑' n, (x n) ^ 2)
    (pairSquareSum_nonneg x) fun k => ?_
  calc
    ∑ n ∈ Finset.range k, pairSquareSum x n ≤
        ∑ n ∈ Finset.range (2 * k), pairSquareSum x n :=
      sum_range_le_sum_range_two_mul (pairSquareSum_nonneg x) k
    _ = 2 * ∑ n ∈ Finset.range (2 * k), (x n) ^ 2 := by
      rw [sum_range_two_mul, sum_range_two_mul]
      simp only [pairSquareSum_even, pairSquareSum_odd]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      ring
    _ ≤ 2 * ∑' n, (x n) ^ 2 := by
      gcongr
      exact (summable_sq_of_mem x).sum_le_tsum _ (fun _ _ => sq_nonneg _)

/-- A bound uniform in time, with a summable right-hand side. -/
theorem U_unb_coord_sq_le (t : ℝ) (x : H_lp) (n : ℕ) :
    (U_unb t x n) ^ 2 ≤ pairSquareSum x n := by
  have hpair := U_unb_preserves_pair_norm_sq (n / 2) t (x : ℕ → ℝ)
  by_cases h : n % 2 = 0
  · have hn : n = 2 * (n / 2) := by omega
    rw [U_unb_apply_coe]
    unfold pairSquareSum
    have heq := congrArg (fun k => (U_unb_fun t (x : ℕ → ℝ) k) ^ 2) hn
    nlinarith [heq, sq_nonneg (U_unb_fun t (x : ℕ → ℝ) (2 * (n / 2) + 1))]
  · have hn : n = 2 * (n / 2) + 1 := by omega
    rw [U_unb_apply_coe]
    unfold pairSquareSum
    have heq := congrArg (fun k => (U_unb_fun t (x : ℕ → ℝ) k) ^ 2) hn
    nlinarith [heq, sq_nonneg (U_unb_fun t (x : ℕ → ℝ) (2 * (n / 2)))]

theorem continuous_U_unb_coord (x : H_lp) (n : ℕ) :
    Continuous (fun t : ℝ => U_unb t x n) := by
  simp only [U_unb_apply_coe, U_unb_fun]
  split_ifs <;> fun_prop

/-- Strong continuity of the displayed isometric group on every Hilbert vector. -/
theorem continuous_U_unb (x : H_lp) : Continuous (fun t : ℝ => U_unb t x) := by
  rw [continuous_iff_continuousAt]
  intro t
  apply tendsto_lp_of_coordinatewise_sq_bound ((summable_pairSquareSum x).mul_left 4)
  · intro n
    exact (continuous_U_unb_coord x n).continuousAt
  · exact Eventually.of_forall fun s n => by
      have hs := U_unb_coord_sq_le s x n
      have ht := U_unb_coord_sq_le t x n
      nlinarith [sq_nonneg (U_unb s x n + U_unb t x n)]

/-- The derivative of each coordinate is the corresponding coordinate of `K_unb_fun`. -/
theorem hasDerivAt_U_unb_coord (x : H_lp) (n : ℕ) :
    HasDerivAt (fun t : ℝ => U_unb t x n) (K_unb_fun (x : ℕ → ℝ) n) 0 := by
  let m := n / 2
  have htheta : HasDerivAt (fun t : ℝ => (m + 1 : ℝ) * t) (m + 1 : ℝ) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul (m + 1 : ℝ)
  have hc := (Real.hasDerivAt_cos ((m + 1 : ℝ) * 0)).comp 0 htheta
  have hs := (Real.hasDerivAt_sin ((m + 1 : ℝ) * 0)).comp 0 htheta
  by_cases h : n % 2 = 0
  · have hn : n = 2 * m := by dsimp [m]; omega
    simp only [hn, U_unb_apply_coe, U_unb_even, K_unb_even]
    convert (hc.mul_const (x (2 * m))).sub (hs.mul_const (x (2 * m + 1))) using 1 <;>
      simp [funext_iff, mul_comm]
  · have hn : n = 2 * m + 1 := by dsimp [m]; omega
    simp only [hn, U_unb_apply_coe, U_unb_odd, K_unb_odd]
    convert (hs.mul_const (x (2 * m))).add (hc.mul_const (x (2 * m + 1))) using 1 <;>
      simp [funext_iff, mul_comm]

private theorem trig_quotient_sq_bounds (a t : ℝ) (ht : t ≠ 0) :
    ((Real.cos (a * t) - 1) / t) ^ 2 ≤ a ^ 2 ∧
      (Real.sin (a * t) / t) ^ 2 ≤ a ^ 2 := by
  have hc : (Real.cos (a * t) - 1) ^ 2 ≤ (a * t) ^ 2 := by
    apply sq_le_sq.mpr
    simpa using Real.abs_cos_sub_cos_le (a * t) 0
  have hs : Real.sin (a * t) ^ 2 ≤ (a * t) ^ 2 := Real.sin_sq_le_sq
  have ht2 : 0 < t ^ 2 := sq_pos_of_ne_zero ht
  constructor
  · rw [div_pow, div_le_iff₀ ht2]
    nlinarith [hc]
  · rw [div_pow, div_le_iff₀ ht2]
    nlinarith [hs]

private theorem linear_combination_sq_le (a c s u v : ℝ)
    (hc : c ^ 2 ≤ a ^ 2) (hs : s ^ 2 ≤ a ^ 2) :
    (c * u + s * v) ^ 2 ≤ 2 * a ^ 2 * (u ^ 2 + v ^ 2) := by
  have hcs : c ^ 2 + s ^ 2 ≤ 2 * a ^ 2 := by linarith
  have hmul := mul_le_mul_of_nonneg_right hcs (add_nonneg (sq_nonneg u) (sq_nonneg v))
  nlinarith [sq_nonneg (c * v - s * u)]

/-- The actual Hilbert-valued difference quotient. -/
def U_unb_differenceQuotient (x : H_lp) (t : ℝ) : H_lp :=
  t⁻¹ • (U_unb t x - x)

theorem U_unb_differenceQuotient_coord_sq_le (x : D_max) (t : ℝ) (ht : t ≠ 0)
    (n : ℕ) :
    (U_unb_differenceQuotient x.1 t n) ^ 2 ≤ 2 * pairSquareSum (K_max x) n := by
  let m := n / 2
  let a : ℝ := m + 1
  let c : ℝ := (Real.cos (a * t) - 1) / t
  let s : ℝ := Real.sin (a * t) / t
  obtain ⟨hc, hs⟩ := trig_quotient_sq_bounds a t ht
  have hK : pairSquareSum (K_max x) n =
      a ^ 2 * ((x.1 (2 * m)) ^ 2 + (x.1 (2 * m + 1)) ^ 2) := by
    simp only [pairSquareSum, K_max_apply_coe, K_unb_even, K_unb_odd]
    dsimp [m, a]
    ring
  rw [hK]
  by_cases h : n % 2 = 0
  · have hn : n = 2 * m := by dsimp [m]; omega
    have heq : U_unb_differenceQuotient x.1 t n =
        c * x.1 (2 * m) + (-s) * x.1 (2 * m + 1) := by
      simp only [U_unb_differenceQuotient, lp.coeFn_smul, Pi.smul_apply,
        lp.coeFn_sub, Pi.sub_apply, smul_eq_mul, hn, U_unb_apply_coe, U_unb_even]
      dsimp [c, s, a]
      ring
    rw [heq]
    simpa only [mul_assoc] using linear_combination_sq_le a c (-s)
      (x.1 (2 * m)) (x.1 (2 * m + 1)) hc (by simpa only [neg_sq] using hs)
  · have hn : n = 2 * m + 1 := by dsimp [m]; omega
    have heq : U_unb_differenceQuotient x.1 t n =
        s * x.1 (2 * m) + c * x.1 (2 * m + 1) := by
      simp only [U_unb_differenceQuotient, lp.coeFn_smul, Pi.smul_apply,
        lp.coeFn_sub, Pi.sub_apply, smul_eq_mul, hn, U_unb_apply_coe, U_unb_odd]
      dsimp [c, s, a]
      ring
    rw [heq]
    simpa only [mul_assoc] using linear_combination_sq_le a s c
      (x.1 (2 * m)) (x.1 (2 * m + 1)) hs hc

/-- Differentiation in the Hilbert norm, on the full maximal graph domain. -/
theorem hasDerivAt_U_unb (x : D_max) :
    HasDerivAt (fun t : ℝ => U_unb t x.1) (K_max x) 0 := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  have hq : Tendsto (U_unb_differenceQuotient x.1) (𝓝[≠] (0 : ℝ)) (𝓝 (K_max x)) := by
    apply tendsto_lp_of_coordinatewise_sq_bound ((summable_pairSquareSum (K_max x)).mul_left 6)
    · intro n
      have h := (hasDerivAt_U_unb_coord x.1 n).tendsto_slope_zero
      simpa only [zero_add, U_unb_zero, ContinuousLinearMap.id_apply,
        U_unb_differenceQuotient, lp.coeFn_smul, Pi.smul_apply, lp.coeFn_sub,
        Pi.sub_apply, K_max_apply_coe] using h
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have ht0 : t ≠ 0 := ht
      intro n
      have hq := U_unb_differenceQuotient_coord_sq_le x t ht0 n
      have hk := coord_sq_le_pairSquareSum (K_max x) n
      nlinarith [sq_nonneg (U_unb_differenceQuotient x.1 t n + K_max x n)]
  convert hq using 1
  ext t n
  simp only [zero_add, U_unb_zero, ContinuousLinearMap.id_apply,
    U_unb_differenceQuotient, lp.coeFn_smul, Pi.smul_apply, lp.coeFn_sub, Pi.sub_apply]

/-- Any strong derivative forces the vector into the actual maximal domain. -/
theorem mem_D_max_of_hasDerivAt_U_unb (x v : H_lp)
    (hv : HasDerivAt (fun t : ℝ => U_unb t x) v 0) : x ∈ D_max := by
  have hcoord (n : ℕ) : v n = K_unb_fun (x : ℕ → ℝ) n := by
    have h := (lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 n).hasFDerivAt.comp_hasDerivAt 0 hv
    exact h.unique (hasDerivAt_U_unb_coord x n)
  change Memℓp (K_unb_fun (x : ℕ → ℝ)) 2
  have heq : K_unb_fun (x : ℕ → ℝ) = (v : ℕ → ℝ) := funext fun n => (hcoord n).symm
  rw [heq]
  exact v.property

/-- Exact domain characterization, rather than a supplied domain certificate. -/
theorem differentiableAt_U_unb_iff (x : H_lp) :
    DifferentiableAt ℝ (fun t : ℝ => U_unb t x) 0 ↔ x ∈ D_max := by
  constructor
  · intro h
    exact mem_D_max_of_hasDerivAt_U_unb x _ h.hasDerivAt
  · intro hx
    exact (hasDerivAt_U_unb ⟨x, hx⟩).differentiableAt

/-- The stronger existing generator interface, instantiated by proved derivatives. -/
def unboundedStrongGenerator :
    TripotentUnboundedResolventFlow.C0GroupGenerator H_lp where
  U := U_unb
  U_zero := U_unb_zero
  U_add := U_unb_add
  D_K := D_max
  K := K_max
  hasDerivAt_gen := hasDerivAt_U_unb
  mem_domain_of_hasDerivAt := mem_D_max_of_hasDerivAt_U_unb
  gen_eq_of_hasDerivAt := fun x _v hv => (hasDerivAt_U_unb x).unique hv

/-- The new concrete instance now supports the existing domain-intertwining theorem. -/
theorem commute_U_unb_implies_domain_intertwining (S : H_lp →L[ℝ] H_lp)
    (hS : ∀ t : ℝ, S.comp (U_unb t) = (U_unb t).comp S) :
    (∀ ⦃x : H_lp⦄, x ∈ D_max → S x ∈ D_max) ∧
      ∀ (h_inv : ∀ ⦃x : H_lp⦄, x ∈ D_max → S x ∈ D_max) (x : D_max),
        S (K_max x) = K_max ⟨S x.1, h_inv x.2⟩ :=
  TripotentUnboundedResolventFlow.c0_group_commute_implies_domain_intertwining
    unboundedStrongGenerator S hS

end InfoGeometry.OperatorAlgebra.UnboundedHilbertResolventAndC0GroupWitness
