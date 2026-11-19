/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Linear
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.LinearAlgebra.Matrix.Notation

namespace InfoGeometry.OperatorAlgebra.UnboundedHilbertResolventAndC0GroupWitness

open scoped ENNReal

abbrev H_lp := lp (fun _ : ℕ => ℝ) 2

instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩

/-! ### Section 1: Pairing Sum Reductions & ℓ² Hilbert Norm Properties -/

lemma sum_range_two_mul (f : ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ Finset.range (2 * N), f n = ∑ m ∈ Finset.range N, (f (2 * m) + f (2 * m + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have h2 : 2 * (N + 1) = 2 * N + 2 := by
      omega
    rw [h2, Finset.sum_range_add, ih]
    rw [Finset.sum_range_succ (fun m => f (2 * m) + f (2 * m + 1))]
    have htwo : ∑ i ∈ Finset.range 2, f (2 * N + i) = f (2 * N) + f (2 * N + 1) := by
      rw [Finset.sum_range_succ, Finset.sum_range_one]
      ring_nf
    rw [htwo]

lemma sum_range_le_sum_range_two_mul {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) (k : ℕ) :
    ∑ n ∈ Finset.range k, f n ≤ ∑ n ∈ Finset.range (2 * k), f n := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro x hx
    rw [Finset.mem_range] at hx ⊢
    omega
  · intro i _ _
    exact hf i

lemma norm_sq_eq_inner (x : H_lp) : ‖x‖^2 = inner ℝ x x := by
  rw [sq, real_inner_self_eq_norm_mul_norm]

lemma inner_self_eq_tsum (x : H_lp) : inner ℝ x x = ∑' n, (x n)^2 := by
  rw [lp.inner_eq_tsum]
  simp only [real_inner_self_eq_norm_mul_norm, Real.norm_eq_abs, abs_mul_abs_self, sq]

lemma norm_sq_eq_tsum (x : H_lp) : ‖x‖^2 = ∑' n, (x n)^2 := by
  rw [norm_sq_eq_inner, inner_self_eq_tsum]

lemma summable_sq_of_mem (x : H_lp) : Summable (fun n => (x n)^2) := by
  have h := lp.summable_inner (𝕜 := ℝ) x x
  have heq : (fun i => inner ℝ (x i) (x i)) = (fun i => (x i)^2) := by
    ext i
    simp only [real_inner_self_eq_norm_mul_norm, Real.norm_eq_abs, abs_mul_abs_self, sq]
  rw [heq] at h
  exact h

lemma memℓp_two_iff (f : ℕ → ℝ) : Memℓp f 2 ↔ Summable (fun n => (f n)^2) := by
  have hp : 0 < (2 : ℝ≥0∞).toReal := by
    norm_num
  rw [memℓp_gen_iff hp]
  have heq : (fun i => ‖f i‖ ^ (2 : ℝ≥0∞).toReal) = (fun i => (f i)^2) := by
    ext i
    have h2 : (2 : ℝ≥0∞).toReal = 2 := by
      norm_num
    rw [h2, Real.norm_eq_abs, Real.rpow_two, sq_abs]
  rw [heq]

/-! ### Section 2: Lifted Continuous Linear Operators on H_lp -/

def s_lp_coeff (m : ℕ) : ℝ :=
  if m % 3 = 0 then 1 else if m % 3 = 1 then -1 else 0

theorem s_lp_coeff_tripotent (m : ℕ) : (s_lp_coeff m)^3 = s_lp_coeff m := by
  dsimp [s_lp_coeff]
  split_ifs <;> ring

theorem s_lp_coeff_sq_le_one (m : ℕ) : (s_lp_coeff m)^2 ≤ 1 := by
  dsimp [s_lp_coeff]
  split_ifs <;> norm_num

def S_lp_fun (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  s_lp_coeff (n / 2) * x n

theorem S_lp_constant_on_pairs (m : ℕ) (x : ℕ → ℝ) :
    S_lp_fun x (2 * m) = s_lp_coeff m * x (2 * m) ∧
    S_lp_fun x (2 * m + 1) = s_lp_coeff m * x (2 * m + 1) := by
  constructor
  · dsimp [S_lp_fun]
    have h : (2 * m) / 2 = m := by
      omega
    rw [h]
  · dsimp [S_lp_fun]
    have h : (2 * m + 1) / 2 = m := by
      omega
    rw [h]

theorem S_lp_fun_tripotent (x : ℕ → ℝ) (n : ℕ) :
    S_lp_fun (S_lp_fun (S_lp_fun x)) n = S_lp_fun x n := by
  dsimp [S_lp_fun]
  have h3 := s_lp_coeff_tripotent (n / 2)
  calc
    s_lp_coeff (n / 2) * (s_lp_coeff (n / 2) * (s_lp_coeff (n / 2) * x n)) =
      (s_lp_coeff (n / 2))^3 * x n := by
        ring
    _ = s_lp_coeff (n / 2) * x n := by
      rw [h3]

lemma summable_S_lp_fun_sq (x : H_lp) : Summable (fun n => (S_lp_fun (x : ℕ → ℝ) n)^2) := by
  refine Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun n => ?_) (summable_sq_of_mem x)
  dsimp [S_lp_fun]
  rw [mul_pow]
  have hle := s_lp_coeff_sq_le_one (n / 2)
  nlinarith [sq_nonneg (x n)]

lemma memℓp_S_lp_fun (x : H_lp) : Memℓp (S_lp_fun (x : ℕ → ℝ)) 2 :=
  (memℓp_two_iff _).2 (summable_S_lp_fun_sq x)

noncomputable def S_lp_linear : H_lp →ₗ[ℝ] H_lp where
  toFun x := ⟨S_lp_fun (x : ℕ → ℝ), memℓp_S_lp_fun x⟩
  map_add' x y := by
    ext n
    simp only [lp.coeFn_add, Pi.add_apply, S_lp_fun, mul_add]
  map_smul' c x := by
    ext n
    simp only [lp.coeFn_smul, Pi.smul_apply, S_lp_fun, smul_eq_mul]
    dsimp
    ring

noncomputable def S_lp : H_lp →L[ℝ] H_lp :=
  S_lp_linear.mkContinuous 1 (fun x => by
    have h_sq : ‖S_lp_linear x‖^2 ≤ ‖x‖^2 := by
      rw [norm_sq_eq_tsum (S_lp_linear x), norm_sq_eq_tsum x]
      refine Summable.tsum_le_tsum (fun n => ?_) (summable_S_lp_fun_sq x) (summable_sq_of_mem x)
      dsimp [S_lp_linear, S_lp_fun]
      rw [mul_pow]
      have hle := s_lp_coeff_sq_le_one (n / 2)
      nlinarith [sq_nonneg (x n)]
    have h_nonneg : 0 ≤ ‖S_lp_linear x‖ := norm_nonneg _
    have hx_nonneg : 0 ≤ ‖x‖ := norm_nonneg _
    have h_le := (sq_le_sq.mp h_sq)
    rw [abs_of_nonneg h_nonneg, abs_of_nonneg hx_nonneg] at h_le
    simpa using h_le)

@[simp]
lemma S_lp_apply_coe (x : H_lp) (n : ℕ) : (S_lp x : ℕ → ℝ) n = s_lp_coeff (n / 2) * x n := by
  have h_apply : S_lp x = S_lp_linear x := LinearMap.mkContinuous_apply _ _ _ x
  rw [h_apply]
  rfl

theorem S_lp_norm_le (x : H_lp) : ‖S_lp x‖ ≤ ‖x‖ := by
  have h_apply : S_lp x = S_lp_linear x := LinearMap.mkContinuous_apply _ _ _ x
  rw [h_apply]
  have h_sq : ‖S_lp_linear x‖^2 ≤ ‖x‖^2 := by
    rw [norm_sq_eq_tsum (S_lp_linear x), norm_sq_eq_tsum x]
    refine Summable.tsum_le_tsum (fun n => ?_) (summable_S_lp_fun_sq x) (summable_sq_of_mem x)
    dsimp [S_lp_linear, S_lp_fun]
    rw [mul_pow]
    have hle := s_lp_coeff_sq_le_one (n / 2)
    nlinarith [sq_nonneg (x n)]
  have h_nonneg : 0 ≤ ‖S_lp_linear x‖ := norm_nonneg _
  have hx_nonneg : 0 ≤ ‖x‖ := norm_nonneg _
  have h_le := (sq_le_sq.mp h_sq)
  rw [abs_of_nonneg h_nonneg, abs_of_nonneg hx_nonneg] at h_le
  exact h_le

theorem S_lp_tripotent : S_lp.comp (S_lp.comp S_lp) = S_lp := by
  ext x n
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, S_lp_apply_coe]
  have h3 := s_lp_coeff_tripotent (n / 2)
  calc
    s_lp_coeff (n / 2) * (s_lp_coeff (n / 2) * (s_lp_coeff (n / 2) * x n)) =
      (s_lp_coeff (n / 2))^3 * x n := by
        ring
    _ = s_lp_coeff (n / 2) * x n := by
      rw [h3]

/-! ### Resolvent Operator R_unb -/

noncomputable def R_unb_fun (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  let m := n / 2
  let d := 1 + (m + 1 : ℝ)^2
  if n % 2 = 0 then
    (x (2 * m) - (m + 1 : ℝ) * x (2 * m + 1)) / d
  else
    ((m + 1 : ℝ) * x (2 * m) + x (2 * m + 1)) / d

theorem R_unb_even (m : ℕ) (x : ℕ → ℝ) :
    R_unb_fun x (2 * m) = (x (2 * m) - (m + 1 : ℝ) * x (2 * m + 1)) / (1 + (m + 1 : ℝ)^2) := by
  dsimp [R_unb_fun]
  split_ifs with h
  · have hdiv : (2 * m) / 2 = m := by
      omega
    rw [hdiv]
  · omega

theorem R_unb_odd (m : ℕ) (x : ℕ → ℝ) :
    R_unb_fun x (2 * m + 1) = ((m + 1 : ℝ) * x (2 * m) + x (2 * m + 1)) / (1 + (m + 1 : ℝ)^2) := by
  dsimp [R_unb_fun]
  split_ifs with h
  · omega
  · have hdiv : (2 * m + 1) / 2 = m := by
      omega
    rw [hdiv]

theorem R_unb_pair_norm_sq_le (m : ℕ) (x : ℕ → ℝ) :
    (R_unb_fun x (2 * m))^2 + (R_unb_fun x (2 * m + 1))^2 ≤ (x (2 * m))^2 + (x (2 * m + 1))^2 := by
  rw [R_unb_even, R_unb_odd]
  set u := x (2 * m)
  set v := x (2 * m + 1)
  set a := (m + 1 : ℝ)
  set d := 1 + a^2
  have hd_pos : 0 < d := by
    dsimp [d]
    positivity
  have hd_ge_one : 1 ≤ d := by
    dsimp [d]
    linarith [sq_nonneg a]
  have h_alg : (u - a * v)^2 / d^2 + (a * u + v)^2 / d^2 = (u^2 + v^2) / d := by
    calc
      (u - a * v)^2 / d^2 + (a * u + v)^2 / d^2 = ((u - a * v)^2 + (a * u + v)^2) / d^2 := by
        ring
      _ = (d * (u^2 + v^2)) / d^2 := by
        dsimp [d]
        ring
      _ = (u^2 + v^2) / d := by
        field_simp [hd_pos.ne']
  rw [div_pow, div_pow, h_alg]
  have h_nonneg : 0 ≤ u^2 + v^2 := by
    positivity
  exact div_le_self h_nonneg hd_ge_one

lemma sum_range_two_mul_R_unb_sq (x : ℕ → ℝ) (k : ℕ) :
    ∑ n ∈ Finset.range (2 * k), (R_unb_fun x n)^2 ≤ ∑ n ∈ Finset.range (2 * k), (x n)^2 := by
  rw [sum_range_two_mul, sum_range_two_mul]
  apply Finset.sum_le_sum
  intro m _
  exact R_unb_pair_norm_sq_le m x

lemma summable_R_unb_fun_sq (x : H_lp) : Summable (fun n => (R_unb_fun (x : ℕ → ℝ) n)^2) := by
  refine summable_of_sum_range_le (c := ∑' n, ((x : ℕ → ℝ) n)^2) (fun _ => sq_nonneg _) (fun k => ?_)
  calc
    ∑ n ∈ Finset.range k, (R_unb_fun (x : ℕ → ℝ) n)^2 ≤
      ∑ n ∈ Finset.range (2 * k), (R_unb_fun (x : ℕ → ℝ) n)^2 := by
        apply sum_range_le_sum_range_two_mul (fun _ => sq_nonneg _)
    _ ≤ ∑ n ∈ Finset.range (2 * k), ((x : ℕ → ℝ) n)^2 :=
      sum_range_two_mul_R_unb_sq (x : ℕ → ℝ) k
    _ ≤ ∑' n, ((x : ℕ → ℝ) n)^2 := by
      exact (summable_sq_of_mem x).sum_le_tsum (Finset.range (2 * k)) (fun i _ => sq_nonneg _)

lemma memℓp_R_unb_fun (x : H_lp) : Memℓp (R_unb_fun (x : ℕ → ℝ)) 2 :=
  (memℓp_two_iff _).2 (summable_R_unb_fun_sq x)

noncomputable def R_unb_linear : H_lp →ₗ[ℝ] H_lp where
  toFun x := ⟨R_unb_fun (x : ℕ → ℝ), memℓp_R_unb_fun x⟩
  map_add' x y := by
    ext n
    simp only [lp.coeFn_add, Pi.add_apply]
    dsimp [R_unb_fun]
    split_ifs <;> ring
  map_smul' c x := by
    ext n
    simp only [lp.coeFn_smul, Pi.smul_apply]
    dsimp [R_unb_fun]
    split_ifs <;> ring

noncomputable def R_unb : H_lp →L[ℝ] H_lp :=
  R_unb_linear.mkContinuous 1 (fun x => by
    have h_sq : ‖R_unb_linear x‖^2 ≤ ‖x‖^2 := by
      rw [norm_sq_eq_tsum (R_unb_linear x), norm_sq_eq_tsum x]
      refine Real.tsum_le_of_sum_range_le (fun _ => sq_nonneg _) (fun k => ?_)
      calc
        ∑ n ∈ Finset.range k, ((R_unb_linear x : ℕ → ℝ) n)^2 ≤
          ∑ n ∈ Finset.range (2 * k), ((R_unb_linear x : ℕ → ℝ) n)^2 := by
            apply sum_range_le_sum_range_two_mul (fun _ => sq_nonneg _)
        _ = ∑ n ∈ Finset.range (2 * k), (R_unb_fun (x : ℕ → ℝ) n)^2 := by
          rfl
        _ ≤ ∑ n ∈ Finset.range (2 * k), ((x : ℕ → ℝ) n)^2 :=
          sum_range_two_mul_R_unb_sq (x : ℕ → ℝ) k
        _ ≤ ∑' n, ((x : ℕ → ℝ) n)^2 :=
          (summable_sq_of_mem x).sum_le_tsum (Finset.range (2 * k)) (fun i _ => sq_nonneg _)
    have h_nonneg : 0 ≤ ‖R_unb_linear x‖ := norm_nonneg _
    have hx_nonneg : 0 ≤ ‖x‖ := norm_nonneg _
    have h_le := (sq_le_sq.mp h_sq)
    rw [abs_of_nonneg h_nonneg, abs_of_nonneg hx_nonneg] at h_le
    simpa using h_le)

@[simp]
lemma R_unb_apply_coe (x : H_lp) (n : ℕ) : (R_unb x : ℕ → ℝ) n = R_unb_fun (x : ℕ → ℝ) n := by
  have h_apply : R_unb x = R_unb_linear x := LinearMap.mkContinuous_apply _ _ _ x
  rw [h_apply]
  rfl

theorem R_unb_norm_le (x : H_lp) : ‖R_unb x‖ ≤ ‖x‖ := by
  have h_apply : R_unb x = R_unb_linear x := LinearMap.mkContinuous_apply _ _ _ x
  rw [h_apply]
  have h_sq : ‖R_unb_linear x‖^2 ≤ ‖x‖^2 := by
    rw [norm_sq_eq_tsum (R_unb_linear x), norm_sq_eq_tsum x]
    refine Real.tsum_le_of_sum_range_le (fun _ => sq_nonneg _) (fun k => ?_)
    calc
      ∑ n ∈ Finset.range k, ((R_unb_linear x : ℕ → ℝ) n)^2 ≤
        ∑ n ∈ Finset.range (2 * k), ((R_unb_linear x : ℕ → ℝ) n)^2 := by
          apply sum_range_le_sum_range_two_mul (fun _ => sq_nonneg _)
      _ = ∑ n ∈ Finset.range (2 * k), (R_unb_fun (x : ℕ → ℝ) n)^2 := by
        rfl
      _ ≤ ∑ n ∈ Finset.range (2 * k), ((x : ℕ → ℝ) n)^2 :=
        sum_range_two_mul_R_unb_sq (x : ℕ → ℝ) k
      _ ≤ ∑' n, ((x : ℕ → ℝ) n)^2 :=
        (summable_sq_of_mem x).sum_le_tsum (Finset.range (2 * k)) (fun i _ => sq_nonneg _)
  have h_nonneg : 0 ≤ ‖R_unb_linear x‖ := norm_nonneg _
  have hx_nonneg : 0 ≤ ‖x‖ := norm_nonneg _
  have h_le := (sq_le_sq.mp h_sq)
  rw [abs_of_nonneg h_nonneg, abs_of_nonneg hx_nonneg] at h_le
  exact h_le

/-! ### Isometric Flow U_unb -/

noncomputable def U_unb_fun (t : ℝ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  let m := n / 2
  let theta := (m + 1 : ℝ) * t
  if n % 2 = 0 then
    Real.cos theta * x (2 * m) - Real.sin theta * x (2 * m + 1)
  else
    Real.sin theta * x (2 * m) + Real.cos theta * x (2 * m + 1)

theorem U_unb_even (m : ℕ) (t : ℝ) (x : ℕ → ℝ) :
    U_unb_fun t x (2 * m) =
    Real.cos ((m + 1 : ℝ) * t) * x (2 * m) - Real.sin ((m + 1 : ℝ) * t) * x (2 * m + 1) := by
  dsimp [U_unb_fun]
  split_ifs with h
  · have hdiv : (2 * m) / 2 = m := by
      omega
    rw [hdiv]
  · omega

theorem U_unb_odd (m : ℕ) (t : ℝ) (x : ℕ → ℝ) :
    U_unb_fun t x (2 * m + 1) =
    Real.sin ((m + 1 : ℝ) * t) * x (2 * m) + Real.cos ((m + 1 : ℝ) * t) * x (2 * m + 1) := by
  dsimp [U_unb_fun]
  split_ifs with h
  · omega
  · have hdiv : (2 * m + 1) / 2 = m := by
      omega
    rw [hdiv]

theorem U_unb_preserves_pair_norm_sq (m : ℕ) (t : ℝ) (x : ℕ → ℝ) :
    (U_unb_fun t x (2 * m))^2 + (U_unb_fun t x (2 * m + 1))^2 =
    (x (2 * m))^2 + (x (2 * m + 1))^2 := by
  rw [U_unb_even, U_unb_odd]
  set c := Real.cos ((m + 1 : ℝ) * t)
  set s := Real.sin ((m + 1 : ℝ) * t)
  set u := x (2 * m)
  set v := x (2 * m + 1)
  have hcs : c^2 + s^2 = 1 := Real.cos_sq_add_sin_sq ((m + 1 : ℝ) * t)
  calc
    (c * u - s * v)^2 + (s * u + c * v)^2 = (c^2 + s^2) * (u^2 + v^2) := by
      ring
    _ = 1 * (u^2 + v^2) := by
      rw [hcs]
    _ = u^2 + v^2 := by
      ring

lemma sum_range_two_mul_U_unb_sq (t : ℝ) (x : ℕ → ℝ) (k : ℕ) :
    ∑ n ∈ Finset.range (2 * k), (U_unb_fun t x n)^2 = ∑ n ∈ Finset.range (2 * k), (x n)^2 := by
  rw [sum_range_two_mul, sum_range_two_mul]
  apply Finset.sum_congr rfl
  intro m _
  exact U_unb_preserves_pair_norm_sq m t x

lemma summable_U_unb_fun_sq (t : ℝ) (x : H_lp) :
    Summable (fun n => (U_unb_fun t (x : ℕ → ℝ) n)^2) := by
  refine summable_of_sum_range_le (c := ∑' n, ((x : ℕ → ℝ) n)^2) (fun _ => sq_nonneg _) (fun k => ?_)
  calc
    ∑ n ∈ Finset.range k, (U_unb_fun t (x : ℕ → ℝ) n)^2 ≤
      ∑ n ∈ Finset.range (2 * k), (U_unb_fun t (x : ℕ → ℝ) n)^2 := by
        apply sum_range_le_sum_range_two_mul (fun _ => sq_nonneg _)
    _ = ∑ n ∈ Finset.range (2 * k), ((x : ℕ → ℝ) n)^2 :=
      sum_range_two_mul_U_unb_sq t (x : ℕ → ℝ) k
    _ ≤ ∑' n, ((x : ℕ → ℝ) n)^2 := by
      exact (summable_sq_of_mem x).sum_le_tsum (Finset.range (2 * k)) (fun i _ => sq_nonneg _)

lemma memℓp_U_unb_fun (t : ℝ) (x : H_lp) : Memℓp (U_unb_fun t (x : ℕ → ℝ)) 2 :=
  (memℓp_two_iff _).2 (summable_U_unb_fun_sq t x)

noncomputable def U_unb_linear (t : ℝ) : H_lp →ₗ[ℝ] H_lp where
  toFun x := ⟨U_unb_fun t (x : ℕ → ℝ), memℓp_U_unb_fun t x⟩
  map_add' x y := by
    ext n
    simp only [lp.coeFn_add, Pi.add_apply]
    dsimp [U_unb_fun]
    split_ifs <;> ring
  map_smul' c x := by
    ext n
    simp only [lp.coeFn_smul, Pi.smul_apply]
    dsimp [U_unb_fun]
    split_ifs <;> ring

noncomputable def U_unb (t : ℝ) : H_lp →L[ℝ] H_lp :=
  (U_unb_linear t).mkContinuous 1 (fun x => by
    have h_sq : ‖U_unb_linear t x‖^2 ≤ ‖x‖^2 := by
      rw [norm_sq_eq_tsum (U_unb_linear t x), norm_sq_eq_tsum x]
      refine Real.tsum_le_of_sum_range_le (fun _ => sq_nonneg _) (fun k => ?_)
      calc
        ∑ n ∈ Finset.range k, ((U_unb_linear t x : ℕ → ℝ) n)^2 ≤
          ∑ n ∈ Finset.range (2 * k), ((U_unb_linear t x : ℕ → ℝ) n)^2 := by
            apply sum_range_le_sum_range_two_mul (fun _ => sq_nonneg _)
        _ = ∑ n ∈ Finset.range (2 * k), (U_unb_fun t (x : ℕ → ℝ) n)^2 := by
          rfl
        _ = ∑ n ∈ Finset.range (2 * k), ((x : ℕ → ℝ) n)^2 :=
          sum_range_two_mul_U_unb_sq t (x : ℕ → ℝ) k
        _ ≤ ∑' n, ((x : ℕ → ℝ) n)^2 :=
          (summable_sq_of_mem x).sum_le_tsum (Finset.range (2 * k)) (fun i _ => sq_nonneg _)
    have h_nonneg : 0 ≤ ‖U_unb_linear t x‖ := norm_nonneg _
    have hx_nonneg : 0 ≤ ‖x‖ := norm_nonneg _
    have h_le := (sq_le_sq.mp h_sq)
    rw [abs_of_nonneg h_nonneg, abs_of_nonneg hx_nonneg] at h_le
    simpa using h_le)

@[simp]
lemma U_unb_apply_coe (t : ℝ) (x : H_lp) (n : ℕ) :
    (U_unb t x : ℕ → ℝ) n = U_unb_fun t (x : ℕ → ℝ) n := by
  have h_apply : U_unb t x = U_unb_linear t x := LinearMap.mkContinuous_apply _ _ _ x
  rw [h_apply]
  rfl

theorem U_unb_norm_le (t : ℝ) (x : H_lp) : ‖U_unb t x‖ ≤ ‖x‖ := by
  have h_apply : U_unb t x = U_unb_linear t x := LinearMap.mkContinuous_apply _ _ _ x
  rw [h_apply]
  have h_sq : ‖U_unb_linear t x‖^2 ≤ ‖x‖^2 := by
    rw [norm_sq_eq_tsum (U_unb_linear t x), norm_sq_eq_tsum x]
    refine Real.tsum_le_of_sum_range_le (fun _ => sq_nonneg _) (fun k => ?_)
    calc
      ∑ n ∈ Finset.range k, ((U_unb_linear t x : ℕ → ℝ) n)^2 ≤
        ∑ n ∈ Finset.range (2 * k), ((U_unb_linear t x : ℕ → ℝ) n)^2 := by
          apply sum_range_le_sum_range_two_mul (fun _ => sq_nonneg _)
      _ = ∑ n ∈ Finset.range (2 * k), (U_unb_fun t (x : ℕ → ℝ) n)^2 := by
        rfl
      _ = ∑ n ∈ Finset.range (2 * k), ((x : ℕ → ℝ) n)^2 :=
        sum_range_two_mul_U_unb_sq t (x : ℕ → ℝ) k
      _ ≤ ∑' n, ((x : ℕ → ℝ) n)^2 :=
        (summable_sq_of_mem x).sum_le_tsum (Finset.range (2 * k)) (fun i _ => sq_nonneg _)
  have h_nonneg : 0 ≤ ‖U_unb_linear t x‖ := norm_nonneg _
  have hx_nonneg : 0 ≤ ‖x‖ := norm_nonneg _
  have h_le := (sq_le_sq.mp h_sq)
  rw [abs_of_nonneg h_nonneg, abs_of_nonneg hx_nonneg] at h_le
  exact h_le

theorem U_unb_zero : U_unb 0 = ContinuousLinearMap.id ℝ H_lp := by
  ext x n
  simp only [U_unb_apply_coe, ContinuousLinearMap.id_apply]
  dsimp [U_unb_fun]
  split_ifs with h
  · have hdiv : 2 * (n / 2) = n := by
      omega
    have htheta : ((n / 2 : ℕ) + 1 : ℝ) * 0 = 0 := by ring
    rw [htheta, Real.cos_zero, Real.sin_zero]
    simp only [one_mul, zero_mul, sub_zero, hdiv]
  · have hdiv : 2 * (n / 2) + 1 = n := by
      omega
    have htheta : ((n / 2 : ℕ) + 1 : ℝ) * 0 = 0 := by ring
    rw [htheta, Real.cos_zero, Real.sin_zero]
    simp only [zero_mul, one_mul, zero_add, hdiv]

theorem U_unb_add (s t : ℝ) : U_unb (s + t) = (U_unb s).comp (U_unb t) := by
  ext x n
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply]
  set m := n / 2
  by_cases h : n % 2 = 0
  · have hn : n = 2 * m := by
      omega
    rw [hn, U_unb_apply_coe, U_unb_even, U_unb_apply_coe, U_unb_even, U_unb_apply_coe, U_unb_apply_coe,
      U_unb_even, U_unb_odd]
    have h_th : ((m : ℕ) + 1 : ℝ) * (s + t) = ((m : ℕ) + 1 : ℝ) * s + ((m : ℕ) + 1 : ℝ) * t := by
      ring
    rw [h_th, Real.cos_add, Real.sin_add]
    ring
  · have hn : n = 2 * m + 1 := by
      omega
    rw [hn, U_unb_apply_coe, U_unb_odd, U_unb_apply_coe, U_unb_odd, U_unb_apply_coe, U_unb_apply_coe,
      U_unb_even, U_unb_odd]
    have h_th : ((m : ℕ) + 1 : ℝ) * (s + t) = ((m : ℕ) + 1 : ℝ) * s + ((m : ℕ) + 1 : ℝ) * t := by
      ring
    rw [h_th, Real.cos_add, Real.sin_add]
    ring

theorem U_unb_isometry (t : ℝ) (x : H_lp) : ‖U_unb t x‖ = ‖x‖ := by
  refine le_antisymm (U_unb_norm_le t x) ?_
  have h_inv : x = U_unb (-t) (U_unb t x) := by
    have h_comp : U_unb (-t + t) = (U_unb (-t)).comp (U_unb t) := U_unb_add (-t) t
    rw [neg_add_cancel, U_unb_zero] at h_comp
    have h_apply := ContinuousLinearMap.ext_iff.mp h_comp x
    simpa only [ContinuousLinearMap.id_apply, ContinuousLinearMap.coe_comp, Function.comp_apply] using h_apply
  nth_rewrite 1 [h_inv]
  exact U_unb_norm_le (-t) (U_unb t x)

/-! ### Section 3: Submodules, Generator and Operator-Norm Unboundedness -/

/-- Dense core domain of finitely supported sequences in ℓ²(ℕ, ℝ). -/
def D_fin : Submodule ℝ H_lp where
  carrier := {x | ∃ N : ℕ, ∀ n ≥ N, (x : ℕ → ℝ) n = 0}
  zero_mem' := ⟨0, fun _ _ => rfl⟩
  add_mem' := by
    rintro x y ⟨Nx, hx⟩ ⟨Ny, hy⟩
    refine ⟨max Nx Ny, fun n hn => ?_⟩
    have hx_zero := hx n (le_of_max_le_left hn)
    have hy_zero := hy n (le_of_max_le_right hn)
    simp only [lp.coeFn_add, Pi.add_apply, hx_zero, hy_zero, add_zero]
  smul_mem' := by
    rintro c x ⟨N, hx⟩
    refine ⟨N, fun n hn => ?_⟩
    simp only [lp.coeFn_smul, Pi.smul_apply, hx n hn, smul_eq_mul, mul_zero]

theorem two_ne_top : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num

theorem D_fin_dense : Dense (D_fin : Set H_lp) := by
  rw [dense_iff_closure_eq, Set.eq_univ_iff_forall]
  intro x
  have h_hasSum := lp.hasSum_single (E := fun _ : ℕ => ℝ) two_ne_top x
  have h_tendsto := h_hasSum.tendsto_sum_nat
  have h_mem (N : ℕ) : (∑ i ∈ Finset.range N, lp.single 2 i ((x : ℕ → ℝ) i)) ∈ D_fin := by
    refine ⟨N, fun n hn => ?_⟩
    simp only [lp.coeFn_sum, Finset.sum_apply]
    have h_zero (i : ℕ) (hi : i ∈ Finset.range N) :
        (lp.single 2 i ((x : ℕ → ℝ) i) : ℕ → ℝ) n = 0 := by
      rw [Finset.mem_range] at hi
      have hne : n ≠ i := by omega
      rw [lp.single_apply, Pi.single_eq_of_ne hne]
    calc
      ∑ i ∈ Finset.range N, (lp.single 2 i ((x : ℕ → ℝ) i) : ℕ → ℝ) n =
        ∑ i ∈ Finset.range N, 0 := by
          apply Finset.sum_congr rfl
          intro i hi
          exact h_zero i hi
      _ = 0 := Finset.sum_const_zero
  exact mem_closure_of_tendsto h_tendsto (Filter.Eventually.of_forall h_mem)

/-- Unbounded skew-adjoint generator K_unb on coordinate pairs. -/
def K_unb_fun (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  if n % 2 = 0 then
    -(((n / 2 : ℕ) + 1 : ℝ) * x (n + 1))
  else
    (((n / 2 : ℕ) + 1 : ℝ) * x (n - 1))

theorem K_unb_even (m : ℕ) (x : ℕ → ℝ) :
    K_unb_fun x (2 * m) = -((m + 1 : ℝ) * x (2 * m + 1)) := by
  dsimp [K_unb_fun]
  split_ifs with h
  · have hdiv : (2 * m) / 2 = m := by
      omega
    rw [hdiv]
  · omega

theorem K_unb_odd (m : ℕ) (x : ℕ → ℝ) :
    K_unb_fun x (2 * m + 1) = (m + 1 : ℝ) * x (2 * m) := by
  dsimp [K_unb_fun]
  split_ifs with h
  · omega
  · have hdiv : (2 * m + 1) / 2 = m := by
      omega
    rw [hdiv]

theorem K_unb_block_skew_adjoint (m : ℕ) (x y : ℕ → ℝ) :
    x (2 * m) * K_unb_fun y (2 * m) + x (2 * m + 1) * K_unb_fun y (2 * m + 1) +
    K_unb_fun x (2 * m) * y (2 * m) + K_unb_fun x (2 * m + 1) * y (2 * m + 1) = 0 := by
  rw [K_unb_even, K_unb_odd, K_unb_even, K_unb_odd]
  ring

/-- Maximal graph domain of K_unb in H_lp. -/
def D_max : Submodule ℝ H_lp where
  carrier := {x : H_lp | Memℓp (K_unb_fun (x : ℕ → ℝ)) 2}
  zero_mem' := by
    have h0 : K_unb_fun (0 : ℕ → ℝ) = 0 := by
      ext n
      dsimp [K_unb_fun]
      split_ifs <;> ring
    change Memℓp (K_unb_fun (0 : ℕ → ℝ)) 2
    rw [h0]
    exact zero_memℓp
  add_mem' := by
    rintro x y hx hy
    change Memℓp (K_unb_fun (x + y : H_lp)) 2
    have h_add : K_unb_fun ((x + y : H_lp) : ℕ → ℝ) =
        K_unb_fun (x : ℕ → ℝ) + K_unb_fun (y : ℕ → ℝ) := by
      ext n
      simp only [lp.coeFn_add, Pi.add_apply]
      dsimp [K_unb_fun]
      split_ifs <;> ring
    rw [h_add]
    exact hx.add hy
  smul_mem' := by
    rintro c x hx
    change Memℓp (K_unb_fun (c • x : H_lp)) 2
    have h_smul : K_unb_fun ((c • x : H_lp) : ℕ → ℝ) =
        c • K_unb_fun (x : ℕ → ℝ) := by
      ext n
      simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
      dsimp [K_unb_fun]
      split_ifs <;> ring
    rw [h_smul]
    exact hx.const_smul c

theorem D_fin_le_D_max : D_fin ≤ D_max := by
  intro x hx
  obtain ⟨N, hN⟩ := hx
  change Memℓp (K_unb_fun (x : ℕ → ℝ)) 2
  rw [memℓp_two_iff]
  have h_supp : Function.support (fun n => (K_unb_fun (x : ℕ → ℝ) n)^2) ⊆ Finset.range (2 * N + 2) := by
    intro n hn
    rw [Function.mem_support] at hn
    rw [Finset.mem_coe, Finset.mem_range]
    by_contra! hge
    have hK : K_unb_fun (x : ℕ → ℝ) n = 0 := by
      dsimp [K_unb_fun]
      split_ifs with h
      · have hx_zero := hN (n + 1) (by omega)
        rw [hx_zero, mul_zero, neg_zero]
      · have hx_zero := hN (n - 1) (by omega)
        rw [hx_zero, mul_zero]
    rw [hK, zero_pow (by norm_num)] at hn
    exact hn rfl
  have h_fin : (Function.support (fun n => (K_unb_fun (x : ℕ → ℝ) n)^2)).Finite :=
    (Finset.finite_toSet (Finset.range (2 * N + 2))).subset h_supp
  exact summable_of_hasFiniteSupport h_fin

/-- Unbounded generator K_max as a linear map from D_max into H_lp. -/
def K_max : D_max →ₗ[ℝ] H_lp where
  toFun x := ⟨K_unb_fun (x.1 : ℕ → ℝ), x.2⟩
  map_add' x y := by
    ext n
    simp only [Submodule.coe_add, lp.coeFn_add, Pi.add_apply]
    dsimp [K_unb_fun]
    split_ifs <;> ring
  map_smul' c x := by
    ext n
    simp only [Submodule.coe_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
    dsimp [K_unb_fun]
    split_ifs <;> ring

@[simp]
lemma K_max_apply_coe (x : D_max) (n : ℕ) :
    (K_max x : ℕ → ℝ) n = K_unb_fun (x.1 : ℕ → ℝ) n := by
  show (K_max x : ℕ → ℝ) n = K_unb_fun (x.1 : ℕ → ℝ) n
  rfl

theorem K_max_skew_symmetric (x y : D_max) :
    inner ℝ (x.1 : H_lp) (K_max y) + inner ℝ (K_max x) (y.1 : H_lp) = 0 := by
  have h1 : inner ℝ (x.1 : H_lp) (K_max y) = ∑' n, (x.1 : ℕ → ℝ) n * K_unb_fun (y.1 : ℕ → ℝ) n := by
    rw [lp.inner_eq_tsum]
    congr 1
    ext n
    exact Real.inner_apply ((x.1 : ℕ → ℝ) n) (K_unb_fun (y.1 : ℕ → ℝ) n)
  have h2 : inner ℝ (K_max x) (y.1 : H_lp) = ∑' n, K_unb_fun (x.1 : ℕ → ℝ) n * (y.1 : ℕ → ℝ) n := by
    rw [lp.inner_eq_tsum]
    congr 1
    ext n
    exact Real.inner_apply (K_unb_fun (x.1 : ℕ → ℝ) n) ((y.1 : ℕ → ℝ) n)
  rw [h1, h2]
  have hf : Summable (fun n => (x.1 : ℕ → ℝ) n * K_unb_fun (y.1 : ℕ → ℝ) n) := by
    have h := lp.summable_inner (𝕜 := ℝ) x.1 (K_max y)
    have heq : (fun i => inner ℝ (x.1 i) ((K_max y) i)) =
        (fun n => (x.1 : ℕ → ℝ) n * K_unb_fun (y.1 : ℕ → ℝ) n) := by
      ext n
      exact Real.inner_apply ((x.1 : ℕ → ℝ) n) (K_unb_fun (y.1 : ℕ → ℝ) n)
    rw [heq] at h
    exact h
  have hg : Summable (fun n => K_unb_fun (x.1 : ℕ → ℝ) n * (y.1 : ℕ → ℝ) n) := by
    have h := lp.summable_inner (𝕜 := ℝ) (K_max x) y.1
    have heq : (fun i => inner ℝ ((K_max x) i) (y.1 i)) =
        (fun n => K_unb_fun (x.1 : ℕ → ℝ) n * (y.1 : ℕ → ℝ) n) := by
      ext n
      exact Real.inner_apply (K_unb_fun (x.1 : ℕ → ℝ) n) ((y.1 : ℕ → ℝ) n)
    rw [heq] at h
    exact h
  rw [← hf.tsum_add hg]
  have h_partial (k : ℕ) :
      ∑ n ∈ Finset.range (2 * k), ((x.1 : ℕ → ℝ) n * K_unb_fun (y.1 : ℕ → ℝ) n +
        K_unb_fun (x.1 : ℕ → ℝ) n * (y.1 : ℕ → ℝ) n) = 0 := by
    rw [sum_range_two_mul]
    have h_zero (m : ℕ) :
        (x.1 : ℕ → ℝ) (2 * m) * K_unb_fun (y.1 : ℕ → ℝ) (2 * m) +
          K_unb_fun (x.1 : ℕ → ℝ) (2 * m) * (y.1 : ℕ → ℝ) (2 * m) +
        ((x.1 : ℕ → ℝ) (2 * m + 1) * K_unb_fun (y.1 : ℕ → ℝ) (2 * m + 1) +
          K_unb_fun (x.1 : ℕ → ℝ) (2 * m + 1) * (y.1 : ℕ → ℝ) (2 * m + 1)) = 0 := by
      have h_adj := K_unb_block_skew_adjoint m (x.1 : ℕ → ℝ) (y.1 : ℕ → ℝ)
      linarith
    calc
      ∑ m ∈ Finset.range k, (((x.1 : ℕ → ℝ) (2 * m) * K_unb_fun (y.1 : ℕ → ℝ) (2 * m) +
            K_unb_fun (x.1 : ℕ → ℝ) (2 * m) * (y.1 : ℕ → ℝ) (2 * m)) +
          ((x.1 : ℕ → ℝ) (2 * m + 1) * K_unb_fun (y.1 : ℕ → ℝ) (2 * m + 1) +
            K_unb_fun (x.1 : ℕ → ℝ) (2 * m + 1) * (y.1 : ℕ → ℝ) (2 * m + 1))) =
        ∑ m ∈ Finset.range k, 0 := by
          apply Finset.sum_congr rfl
          intro m _
          exact h_zero m
      _ = 0 := Finset.sum_const_zero
  have h_tendsto := (hf.add hg).hasSum.tendsto_sum_nat
  have h_two_k : Filter.Tendsto (fun k => 2 * k) Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop_mono (f := fun (k : ℕ) => k) (g := fun k => 2 * k) (fun k => by omega) ?_
    exact Filter.tendsto_id
  have h_subseq := h_tendsto.comp h_two_k
  change Filter.Tendsto (fun k => ∑ n ∈ Finset.range (2 * k),
      ((x.1 : ℕ → ℝ) n * K_unb_fun (y.1 : ℕ → ℝ) n +
        K_unb_fun (x.1 : ℕ → ℝ) n * (y.1 : ℕ → ℝ) n))
    Filter.atTop (nhds (∑' n, ((x.1 : ℕ → ℝ) n * K_unb_fun (y.1 : ℕ → ℝ) n +
      K_unb_fun (x.1 : ℕ → ℝ) n * (y.1 : ℕ → ℝ) n))) at h_subseq
  have h_const : (fun k => ∑ n ∈ Finset.range (2 * k),
      ((x.1 : ℕ → ℝ) n * K_unb_fun (y.1 : ℕ → ℝ) n +
        K_unb_fun (x.1 : ℕ → ℝ) n * (y.1 : ℕ → ℝ) n)) = fun _ => 0 := by
    ext k
    exact h_partial k
  rw [h_const] at h_subseq
  exact tendsto_nhds_unique h_subseq tendsto_const_nhds

theorem K_max_is_unbounded :
    ¬ ∃ C : ℝ, ∀ x : D_max, ‖K_max x‖ ≤ C * ‖(x : H_lp)‖ := by
  rintro ⟨C, hC⟩
  have h_contra (m : ℕ) : (m + 1 : ℝ) ≤ C := by
    have he_mem_fin : (lp.single 2 (2 * m) (1 : ℝ) : H_lp) ∈ D_fin := by
      refine ⟨2 * m + 1, fun n hn => ?_⟩
      rw [lp.single_apply, Pi.single_eq_of_ne (by omega)]
    have he_mem_max : (lp.single 2 (2 * m) (1 : ℝ) : H_lp) ∈ D_max :=
      D_fin_le_D_max he_mem_fin
    have h_le := hC ⟨lp.single 2 (2 * m) (1 : ℝ), he_mem_max⟩
    have hp : 0 < (2 : ℝ≥0∞) := by norm_num
    have h_norm_e : ‖(lp.single 2 (2 * m) (1 : ℝ) : H_lp)‖ = 1 := by
      rw [lp.norm_single hp, norm_one]
    have h_K_norm : ‖K_max ⟨lp.single 2 (2 * m) (1 : ℝ), he_mem_max⟩‖ = m + 1 := by
      have heq : K_max ⟨lp.single 2 (2 * m) (1 : ℝ), he_mem_max⟩ =
          (m + 1 : ℝ) • lp.single 2 (2 * m + 1) (1 : ℝ) := by
        ext n
        simp only [K_max_apply_coe, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
        dsimp [K_unb_fun]
        by_cases hn : n = 2 * m + 1
        · rw [hn]
          have hdiv : (2 * m + 1) / 2 = m := by omega
          have hsub : 2 * m + 1 - 1 = 2 * m := by omega
          split_ifs with h_even
          · omega
          · rw [hdiv, hsub, Pi.single_eq_same, Pi.single_eq_same]
        · by_cases h_even : n % 2 = 0
          · split_ifs
            have hne : n + 1 ≠ 2 * m := by omega
            have hne2 : n ≠ 2 * m + 1 := hn
            rw [Pi.single_eq_of_ne hne, Pi.single_eq_of_ne hne2]
            ring
          · split_ifs
            have hne : n - 1 ≠ 2 * m := by omega
            have hne2 : n ≠ 2 * m + 1 := hn
            rw [Pi.single_eq_of_ne hne, Pi.single_eq_of_ne hne2]
            ring
      rw [heq, norm_smul, lp.norm_single hp, norm_one, mul_one, Real.norm_eq_abs,
        abs_of_nonneg (by positivity)]
    rw [h_K_norm, h_norm_e, mul_one] at h_le
    exact h_le
  obtain ⟨N, hN⟩ := exists_nat_gt C
  have h_le := h_contra N
  linarith

/-! ### Section 4: Non-Trivial Instances and Domain Intertwining -/

/-- Abstract resolvent data package for an unbounded operator K on H. -/
structure ResolventData (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H] where
  D_K : Submodule ℝ H
  K : D_K →ₗ[ℝ] H
  R : H →L[ℝ] H
  R_in_domain : ∀ x : H, R x ∈ D_K
  sub_K_R_apply : ∀ x : H, (R x : H) - K ⟨R x, R_in_domain x⟩ = x
  R_sub_K_apply : ∀ (x : H) (hx : x ∈ D_K), R (x - K ⟨x, hx⟩) = x

/-- Abstract C₀-group generator data package on a Hilbert space H. -/
structure C0GroupGenerator (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] where
  U : ℝ → (H →L[ℝ] H)
  U_zero : U 0 = ContinuousLinearMap.id ℝ H
  U_add : ∀ s t : ℝ, U (s + t) = (U s).comp (U t)
  U_isometry : ∀ (t : ℝ) (x : H), ‖U t x‖ = ‖x‖
  D_K : Submodule ℝ H
  K : D_K →ₗ[ℝ] H
  D_dense : Dense (D_K : Set H)
  K_skew_symmetric : ∀ x y : D_K, inner ℝ (x.1 : H) (K y) + inner ℝ (K x) (y.1 : H) = 0

theorem D_max_dense : Dense (D_max : Set H_lp) :=
  D_fin_dense.mono D_fin_le_D_max

lemma K_unb_R_unb_pair_norm_sq_le (m : ℕ) (x : ℕ → ℝ) :
    (K_unb_fun (R_unb_fun x) (2 * m))^2 + (K_unb_fun (R_unb_fun x) (2 * m + 1))^2 ≤
    (x (2 * m))^2 + (x (2 * m + 1))^2 := by
  rw [K_unb_even, K_unb_odd, R_unb_even, R_unb_odd]
  set u := x (2 * m)
  set v := x (2 * m + 1)
  set a := (m + 1 : ℝ)
  set d := 1 + a^2
  have hd_pos : 0 < d := by
    dsimp [d]
    positivity
  have hd_ge : a^2 ≤ d := by
    dsimp [d]
    linarith
  have h_alg : (- (a * ((a * u + v) / d)))^2 + (a * ((u - a * v) / d))^2 =
      (a^2 / d) * (u^2 + v^2) := by
    have hd_ne : d ≠ 0 := hd_pos.ne'
    dsimp [d]
    field_simp [hd_ne]
    ring
  rw [h_alg]
  have h_ratio_le_one : a^2 / d ≤ 1 := by
    exact (div_le_one hd_pos).mpr hd_ge
  have h_sum_nonneg : 0 ≤ u^2 + v^2 := by
    positivity
  nlinarith

lemma sum_range_two_mul_K_unb_R_unb_sq (x : ℕ → ℝ) (k : ℕ) :
    ∑ n ∈ Finset.range (2 * k), (K_unb_fun (R_unb_fun x) n)^2 ≤ ∑ n ∈ Finset.range (2 * k), (x n)^2 := by
  rw [sum_range_two_mul, sum_range_two_mul]
  apply Finset.sum_le_sum
  intro m _
  exact K_unb_R_unb_pair_norm_sq_le m x

lemma summable_K_unb_R_unb_sq (x : H_lp) :
    Summable (fun n => (K_unb_fun (R_unb x : ℕ → ℝ) n)^2) := by
  have h_coe : (R_unb x : ℕ → ℝ) = R_unb_fun (x : ℕ → ℝ) := by
    ext k
    exact R_unb_apply_coe x k
  have heq : (fun n => (K_unb_fun (R_unb x : ℕ → ℝ) n)^2) =
      (fun n => (K_unb_fun (R_unb_fun (x : ℕ → ℝ)) n)^2) := by
    rw [h_coe]
  rw [heq]
  refine summable_of_sum_range_le (c := ∑' n, ((x : ℕ → ℝ) n)^2) (fun _ => sq_nonneg _) (fun k => ?_)
  calc
    ∑ n ∈ Finset.range k, (K_unb_fun (R_unb_fun (x : ℕ → ℝ)) n)^2 ≤
      ∑ n ∈ Finset.range (2 * k), (K_unb_fun (R_unb_fun (x : ℕ → ℝ)) n)^2 := by
        apply sum_range_le_sum_range_two_mul (fun _ => sq_nonneg _)
    _ ≤ ∑ n ∈ Finset.range (2 * k), ((x : ℕ → ℝ) n)^2 :=
      sum_range_two_mul_K_unb_R_unb_sq (x : ℕ → ℝ) k
    _ ≤ ∑' n, ((x : ℕ → ℝ) n)^2 :=
      (summable_sq_of_mem x).sum_le_tsum (Finset.range (2 * k)) (fun i _ => sq_nonneg _)

theorem R_unb_in_D_max (x : H_lp) : R_unb x ∈ D_max := by
  change Memℓp (K_unb_fun (R_unb x : ℕ → ℝ)) 2
  rw [memℓp_two_iff]
  exact summable_K_unb_R_unb_sq x

theorem R_unb_sub_K_apply (x : H_lp) :
    (R_unb x : H_lp) - K_max ⟨R_unb x, R_unb_in_D_max x⟩ = x := by
  ext n
  by_cases h_even : n % 2 = 0
  · set m := n / 2
    have hn : n = 2 * m := by
      omega
    rw [hn]
    simp only [lp.coeFn_sub, Pi.sub_apply, R_unb_apply_coe, K_max_apply_coe]
    rw [K_unb_even, R_unb_even, R_unb_apply_coe, R_unb_odd]
    set u := (x : ℕ → ℝ) (2 * m)
    set v := (x : ℕ → ℝ) (2 * m + 1)
    set a := (m + 1 : ℝ)
    set d := 1 + a^2
    have hd_ne : d ≠ 0 := by
      dsimp [d]
      positivity
    calc
      (u - a * v) / d - - (a * ((a * u + v) / d)) =
        ((u - a * v) + a * (a * u + v)) / d := by
          ring
      _ = (d * u) / d := by
        dsimp [d]
        ring
      _ = u := by
        exact mul_div_cancel_left₀ u hd_ne
  · set m := n / 2
    have hn : n = 2 * m + 1 := by
      omega
    rw [hn]
    simp only [lp.coeFn_sub, Pi.sub_apply, R_unb_apply_coe, K_max_apply_coe]
    rw [K_unb_odd, R_unb_odd, R_unb_apply_coe, R_unb_even]
    set u := (x : ℕ → ℝ) (2 * m)
    set v := (x : ℕ → ℝ) (2 * m + 1)
    set a := (m + 1 : ℝ)
    set d := 1 + a^2
    have hd_ne : d ≠ 0 := by
      dsimp [d]
      positivity
    calc
      (a * u + v) / d - a * ((u - a * v) / d) =
        ((a * u + v) - a * (u - a * v)) / d := by
          ring
      _ = (d * v) / d := by
        dsimp [d]
        ring
      _ = v := by
        exact mul_div_cancel_left₀ v hd_ne

theorem R_unb_sub_K_apply' (x : H_lp) (hx : x ∈ D_max) :
    R_unb (x - K_max ⟨x, hx⟩) = x := by
  ext n
  by_cases h_even : n % 2 = 0
  · set m := n / 2
    have hn : n = 2 * m := by
      omega
    rw [hn, R_unb_apply_coe, R_unb_even]
    simp only [lp.coeFn_sub, Pi.sub_apply, K_max_apply_coe]
    rw [K_unb_even, K_unb_odd]
    set u := (x : ℕ → ℝ) (2 * m)
    set v := (x : ℕ → ℝ) (2 * m + 1)
    set a := (m + 1 : ℝ)
    set d := 1 + a^2
    have hd_ne : d ≠ 0 := by
      dsimp [d]
      positivity
    calc
      ((u - - (a * v)) - a * (v - a * u)) / d =
        (d * u) / d := by
          dsimp [d]
          ring
      _ = u := by
        exact mul_div_cancel_left₀ u hd_ne
  · set m := n / 2
    have hn : n = 2 * m + 1 := by
      omega
    rw [hn, R_unb_apply_coe, R_unb_odd]
    simp only [lp.coeFn_sub, Pi.sub_apply, K_max_apply_coe]
    rw [K_unb_even, K_unb_odd]
    set u := (x : ℕ → ℝ) (2 * m)
    set v := (x : ℕ → ℝ) (2 * m + 1)
    set a := (m + 1 : ℝ)
    set d := 1 + a^2
    have hd_ne : d ≠ 0 := by
      dsimp [d]
      positivity
    calc
      (a * (u - - (a * v)) + (v - a * u)) / d =
        (d * v) / d := by
          dsimp [d]
          ring
      _ = v := by
        exact mul_div_cancel_left₀ v hd_ne

/-- Concrete non-trivial resolvent data for the unbounded operator K_max on H_lp. -/
noncomputable def unboundedResolventData : ResolventData H_lp where
  D_K := D_max
  K := K_max
  R := R_unb
  R_in_domain := R_unb_in_D_max
  sub_K_R_apply := R_unb_sub_K_apply
  R_sub_K_apply := R_unb_sub_K_apply'

/-- Concrete non-trivial C₀-group generator data for the unbounded operator K_max on H_lp. -/
noncomputable def unboundedC0Group : C0GroupGenerator H_lp where
  U := U_unb
  U_zero := U_unb_zero
  U_add := U_unb_add
  U_isometry := U_unb_isometry
  D_K := D_max
  K := K_max
  D_dense := D_max_dense
  K_skew_symmetric := K_max_skew_symmetric

/-- Domain preservation predicate for an operator S on a submodule D_K. -/
def PreservesDomain (S : H_lp →L[ℝ] H_lp) (D_K : Submodule ℝ H_lp) : Prop :=
  ∀ ⦃x : H_lp⦄, x ∈ D_K → S x ∈ D_K

lemma K_unb_fun_S_lp_fun (x : ℕ → ℝ) (n : ℕ) :
    K_unb_fun (S_lp_fun x) n = s_lp_coeff (n / 2) * K_unb_fun x n := by
  dsimp [K_unb_fun, S_lp_fun]
  by_cases h_even : n % 2 = 0
  · split_ifs
    have hdiv : (n + 1) / 2 = n / 2 := by
      omega
    rw [hdiv]
    ring
  · split_ifs
    have hdiv : (n - 1) / 2 = n / 2 := by
      omega
    rw [hdiv]
    ring

theorem S_lp_preserves_D_max : PreservesDomain S_lp D_max := by
  intro x hx
  change Memℓp (K_unb_fun (x : ℕ → ℝ)) 2 at hx
  rw [memℓp_two_iff] at hx
  change Memℓp (K_unb_fun (S_lp x : ℕ → ℝ)) 2
  rw [memℓp_two_iff]
  have h_coe : (S_lp x : ℕ → ℝ) = S_lp_fun (x : ℕ → ℝ) := by
    ext k
    exact S_lp_apply_coe x k
  have heq : (fun n => (K_unb_fun (S_lp x : ℕ → ℝ) n)^2) =
      (fun n => (s_lp_coeff (n / 2))^2 * (K_unb_fun (x : ℕ → ℝ) n)^2) := by
    ext n
    rw [h_coe, K_unb_fun_S_lp_fun]
    ring
  rw [heq]
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun n => ?_) hx
  have h_coeff := s_lp_coeff_sq_le_one (n / 2)
  have h_sq_nonneg : 0 ≤ (K_unb_fun (x : ℕ → ℝ) n)^2 := by
    positivity
  nlinarith

theorem S_lp_K_max_commute (x : D_max) :
    S_lp (K_max x) = K_max ⟨S_lp x.1, S_lp_preserves_D_max x.2⟩ := by
  ext n
  have h_fun : (S_lp x.1 : ℕ → ℝ) = S_lp_fun (x.1 : ℕ → ℝ) := by
    ext k
    exact S_lp_apply_coe x.1 k
  calc
    (S_lp (K_max x) : ℕ → ℝ) n = s_lp_coeff (n / 2) * K_unb_fun (x.1 : ℕ → ℝ) n := by
      rw [S_lp_apply_coe]
      rfl
    _ = (K_max ⟨S_lp x.1, S_lp_preserves_D_max x.2⟩ : ℕ → ℝ) n := by
      rw [K_max_apply_coe, h_fun, K_unb_fun_S_lp_fun]

theorem unbounded_kato_trotter_witness :
    S_lp.comp R_unb = R_unb.comp S_lp ∧
    (∀ t : ℝ, S_lp.comp (U_unb t) = (U_unb t).comp S_lp) := by
  refine ⟨?_, fun t => ?_⟩
  · ext x n
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply]
    have h_lhs : (S_lp (R_unb x) : ℕ → ℝ) n = s_lp_coeff (n / 2) * R_unb_fun (x : ℕ → ℝ) n := by
      rw [S_lp_apply_coe]
      rfl
    rw [h_lhs, R_unb_apply_coe]
    by_cases h_even : n % 2 = 0
    · set m := n / 2
      have hn : n = 2 * m := by
        omega
      have hdiv1 : (2 * m) / 2 = m := by
        omega
      have hdiv2 : (2 * m + 1) / 2 = m := by
        omega
      rw [hn, R_unb_even, R_unb_even]
      rw [S_lp_apply_coe, S_lp_apply_coe]
      dsimp [S_lp_fun]
      rw [hdiv1, hdiv2]
      ring
    · set m := n / 2
      have hn : n = 2 * m + 1 := by
        omega
      have hdiv1 : (2 * m) / 2 = m := by
        omega
      have hdiv2 : (2 * m + 1) / 2 = m := by
        omega
      rw [hn, R_unb_odd, R_unb_odd]
      rw [S_lp_apply_coe, S_lp_apply_coe]
      dsimp [S_lp_fun]
      rw [hdiv1, hdiv2]
      ring
  · ext x n
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply]
    have h_lhs : (S_lp (U_unb t x) : ℕ → ℝ) n = s_lp_coeff (n / 2) * U_unb_fun t (x : ℕ → ℝ) n := by
      rw [S_lp_apply_coe]
      rfl
    rw [h_lhs, U_unb_apply_coe]
    by_cases h_even : n % 2 = 0
    · set m := n / 2
      have hn : n = 2 * m := by
        omega
      have hdiv1 : (2 * m) / 2 = m := by
        omega
      have hdiv2 : (2 * m + 1) / 2 = m := by
        omega
      rw [hn, U_unb_even, U_unb_even]
      rw [S_lp_apply_coe, S_lp_apply_coe]
      dsimp [S_lp_fun]
      rw [hdiv1, hdiv2]
      ring
    · set m := n / 2
      have hn : n = 2 * m + 1 := by
        omega
      have hdiv1 : (2 * m) / 2 = m := by
        omega
      have hdiv2 : (2 * m + 1) / 2 = m := by
        omega
      rw [hn, U_unb_odd, U_unb_odd]
      rw [S_lp_apply_coe, S_lp_apply_coe]
      dsimp [S_lp_fun]
      rw [hdiv1, hdiv2]
      ring

theorem S_lp_five_grade_invariance (lam : ℝ) (v : H_lp) (hv : S_lp v = lam • v) (t : ℝ) :
    S_lp (U_unb t v) = lam • (U_unb t v) := by
  have h_comm : S_lp (U_unb t v) = U_unb t (S_lp v) := by
    have h := ContinuousLinearMap.ext_iff.mp (unbounded_kato_trotter_witness.2 t) v
    simpa only [ContinuousLinearMap.coe_comp, Function.comp_apply] using h
  rw [h_comm, hv, map_smul]

/-! ### Section 5: OpenGauss T16 Non-Commutativity Witness -/

noncomputable instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩

/-- Elementary unit operator E_{i, j} mapping x to x(j) • e_i. -/
noncomputable def E_unit (i j : ℕ) : H_lp →L[ℝ] H_lp :=
  ContinuousLinearMap.smulRight (lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 j) (lp.single 2 i (1 : ℝ))

@[simp]
lemma E_unit_apply (i j : ℕ) (x : H_lp) :
    E_unit i j x = (x : ℕ → ℝ) j • lp.single 2 i (1 : ℝ) := by
  dsimp [E_unit]
  rfl

theorem lp_operator_noncommuting :
    ∃ A B : H_lp →L[ℝ] H_lp, A.comp B ≠ B.comp A := by
  use E_unit 0 1, E_unit 1 0
  intro h_comm
  have h_ev := ContinuousLinearMap.ext_iff.mp h_comm (lp.single 2 0 (1 : ℝ))
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, E_unit_apply,
    lp.coeFn_smul, Pi.smul_apply, smul_eq_mul] at h_ev
  have h_00 : (lp.single 2 0 (1 : ℝ) : ℕ → ℝ) 0 = 1 := by
    rw [lp.single_apply, Pi.single_eq_same]
  have h_01 : (lp.single 2 0 (1 : ℝ) : ℕ → ℝ) 1 = 0 := by
    rw [lp.single_apply, Pi.single_eq_of_ne (by omega)]
  have h_11 : (lp.single 2 1 (1 : ℝ) : ℕ → ℝ) 1 = 1 := by
    rw [lp.single_apply, Pi.single_eq_same]
  rw [h_00, h_11, h_01] at h_ev
  ring_nf at h_ev
  rw [one_smul, zero_smul] at h_ev
  have h_coord := congr_fun (congr_arg Subtype.val h_ev) 0
  rw [h_00, lp.coeFn_zero, Pi.zero_apply] at h_coord
  exact one_ne_zero h_coord

end InfoGeometry.OperatorAlgebra.UnboundedHilbertResolventAndC0GroupWitness
