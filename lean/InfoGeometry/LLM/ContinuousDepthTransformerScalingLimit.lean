/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.LLM.KreinPositionalThermodynamicAttention
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-!
# Continuous-Depth Transformer Scaling Limit, Grönwall Convergence & Attention Consensus Decay

Advances Frontier 4 ("Continuous-depth transformer scaling limits") with two coupled, kernel-checked
continuous-depth analytic theorems built over `InfoGeometry.LLM.KreinPositionalThermodynamicAttention`:

1. **Discrete Depth-`L` Residual Flow to Neural ODE Limit (`L → ∞`)**:
   - Defines explicit step-$1/L$ residual Euler updates `residualStep` and depth-$L$ trajectory
     `residualFlow L T V x₀`.
   - Proves the exact discrete Grönwall inequality (`discrete_gronwall_bound`), local `O(h^2)`
     truncation bound (`local_euler_truncation_bound`) via Mathlib's vector-valued Mean Value
     Theorem, global `O(1/L) * exp(M T)` error bound (`residualFlow_global_error_le`), and strong
     convergence to the continuous-depth Neural ODE solution (`tendsto_residualFlow_continuous_depth`).
2. **Continuous-Depth Softmax Attention Consensus & Exponential Variance Collapse (`t → ∞`)**:
   - Connects `softmaxAttnKernel` directly to `KreinPositionalThermodynamicAttention.tempGibbsWeight`,
     proving strict positivity (`softmaxAttnKernel_pos`) and row-stochasticity (`softmaxAttnKernel_row_sum_one`).
   - Proves exact token center-of-mass conservation (`hasDerivAt_centerOfMass_zero_of_doublyStochastic`),
     Dirichlet energy dissipation (`hasDerivAt_cloudEnergy_eq_neg_dirichlet`,
     `hasDerivAt_cloudVariance_eq_neg_dirichlet`) for symmetric row-stochastic attention kernels, and
     exponential consensus decay under a uniform Doeblin lower bound `δ > 0`:
     `cloudVariance (X t) ≤ cloudVariance (X 0) * Real.exp (-2 * N * δ * t)` (`cloudVariance_le_exp_decay`)
     and `Tendsto (fun t => cloudVariance (X t)) atTop (𝓝 0)` (`cloudVariance_tendsto_zero`).

## Three-Bucket Audit Map

#### BUCKET 1: CLOSED FINITE & ANALYTIC THEOREMS
* `discrete_gronwall_bound`, `local_euler_truncation_bound`, `residualFlow_global_error_le`,
  `tendsto_residualFlow_continuous_depth`.
* `softmaxAttnKernel_pos`, `softmaxAttnKernel_row_sum_one`, `hasDerivAt_centerOfMass_zero_of_doublyStochastic`,
  `hasDerivAt_cloudEnergy_eq_neg_dirichlet`, `hasDerivAt_cloudVariance_eq_neg_dirichlet`,
  `hasDerivAt_cloudVariance_le_exp_rate`, `cloudVariance_le_exp_decay`, `cloudVariance_tendsto_zero`.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES
* `tendsto_residualFlow_continuous_depth` conditional on `M`-Lipschitz vector field `V` and an ODE
  solution `x` on `[0, T]` with `‖V(x(s))‖ ≤ B`; `cloudVariance_tendsto_zero` conditional on a
  symmetric row-stochastic attention flow `X(t)` satisfying `∀ i j, δ ≤ P(X(t)) i j`.

#### BUCKET 3: OPEN CLOSURE DEBT
* Global well-posedness and sharp metastable phase characterization for general asymmetric,
  non-Doeblin (`δ = 0` or causal-masked) multi-layer transformers remain active open directions.
-/

noncomputable section

namespace InfoGeometry.LLM.ContinuousDepthTransformerScalingLimit

open scoped BigOperators
open Filter Topology
open InfoGeometry.LLM.KreinPositionalThermodynamicAttention

/-! ## 1. Discrete Depth-`L` Residual Flow & Exact Grönwall Neural-ODE Convergence (`L → ∞`) -/

/-- Single depth-normalized residual Euler step `x ↦ x + h • V x`. -/
def residualStep {E : Type*} [AddCommGroup E] [Module ℝ E] (h : ℝ) (V : E → E) (x : E) : E :=
  x + h • V x

/-- Depth-`L` residual transformer trajectory with step size `T / L` starting at `x₀`. -/
def residualFlow {E : Type*} [AddCommGroup E] [Module ℝ E]
    (L : ℕ) (T : ℝ) (V : E → E) (x₀ : E) : ℕ → E
  | 0 => x₀
  | k + 1 => residualStep (T / (L : ℝ)) V (residualFlow L T V x₀ k)

/-- Discrete Grönwall inequality without division by `a`:
`e 0 = 0` and `e (k + 1) ≤ (1 + a) * e k + b` imply `a * e k ≤ b * ((1 + a) ^ k - 1)`. -/
theorem discrete_gronwall_bound {a b : ℝ} (ha : 0 ≤ a) (e : ℕ → ℝ)
    (he0 : e 0 = 0) (hstep : ∀ k : ℕ, e (k + 1) ≤ (1 + a) * e k + b) :
    ∀ k : ℕ, a * e k ≤ b * ((1 + a) ^ k - 1) := by
  intro k
  induction k with
  | zero =>
    simp [he0]
  | succ k ih =>
    have h1a : 0 ≤ 1 + a := by linarith
    have hmul : a * e (k + 1) ≤ a * ((1 + a) * e k + b) :=
      mul_le_mul_of_nonneg_left (hstep k) ha
    have hih_mul : (1 + a) * (a * e k) ≤ (1 + a) * (b * ((1 + a) ^ k - 1)) :=
      mul_le_mul_of_nonneg_left ih h1a
    calc
      a * e (k + 1) ≤ (1 + a) * (a * e k) + a * b := by nlinarith
      _ ≤ (1 + a) * (b * ((1 + a) ^ k - 1)) + a * b := by linarith
      _ = b * ((1 + a) ^ (k + 1) - 1) := by
        rw [pow_succ']
        ring

/-- Local `O(h²)` Euler truncation bound for an `M`-Lipschitz ODE `x' = V(x)` with `‖V(x)‖ ≤ B`. -/
theorem local_euler_truncation_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : E → E) {M B h t₀ : ℝ}
    (hM : 0 ≤ M) (hB : 0 ≤ B) (hh : 0 ≤ h)
    (hLip : ∀ u v : E, ‖V u - V v‖ ≤ M * ‖u - v‖)
    (x : ℝ → E)
    (hode : ∀ s ∈ Set.Icc t₀ (t₀ + h), HasDerivAt x (V (x s)) s ∧ ‖V (x s)‖ ≤ B) :
    ‖x (t₀ + h) - residualStep h V (x t₀)‖ ≤ M * B * h ^ 2 := by
  have ht0_mem : t₀ ∈ Set.Icc t₀ (t₀ + h) := ⟨le_rfl, by linarith⟩
  have hth_mem : t₀ + h ∈ Set.Icc t₀ (t₀ + h) := ⟨by linarith, le_rfl⟩
  have hx_lip : ∀ s ∈ Set.Icc t₀ (t₀ + h), ‖x s - x t₀‖ ≤ B * h := by
    intro s hs
    have hsub_s : Set.Icc t₀ s ⊆ Set.Icc t₀ (t₀ + h) := Set.Icc_subset_Icc_right hs.2
    have hderiv_s : ∀ u ∈ Set.Icc t₀ s, HasDerivWithinAt x (V (x u)) (Set.Icc t₀ s) u :=
      fun u hu => (hode u (hsub_s hu)).1.hasDerivWithinAt
    have hbd_s : ∀ u ∈ Set.Icc t₀ s, ‖V (x u)‖ ≤ B :=
      fun u hu => (hode u (hsub_s hu)).2
    have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv_s hbd_s
      (convex_Icc t₀ s) ⟨le_rfl, hs.1⟩ ⟨hs.1, le_rfl⟩
    have hsnorm : ‖s - t₀‖ = s - t₀ := by
      rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hs.1)]
    rw [hsnorm] at hmvt
    have hsh : B * (s - t₀) ≤ B * h :=
      mul_le_mul_of_nonneg_left (by linarith [hs.2]) hB
    exact hmvt.trans hsh
  let g : ℝ → E := fun s => x s - x t₀ - (s - t₀) • V (x t₀)
  have hg_deriv : ∀ s ∈ Set.Icc t₀ (t₀ + h),
      HasDerivWithinAt g (V (x s) - V (x t₀)) (Set.Icc t₀ (t₀ + h)) s := by
    intro s hs
    have hx_d := (hode s hs).1
    have hlin : HasDerivAt (fun u : ℝ => x t₀ + (u - t₀) • V (x t₀)) (V (x t₀)) s := by
      have hsub : HasDerivAt (fun u : ℝ => u - t₀) 1 s := (hasDerivAt_id s).sub_const t₀
      have hsm := hsub.smul_const (V (x t₀))
      simpa using hsm.const_add (x t₀)
    have hsub_d : HasDerivAt (fun u => x u - (x t₀ + (u - t₀) • V (x t₀))) (V (x s) - V (x t₀)) s :=
      hx_d.sub hlin
    have hgeq : g = fun u => x u - (x t₀ + (u - t₀) • V (x t₀)) := by
      funext u
      dsimp [g]
      abel
    rw [hgeq]
    exact hsub_d.hasDerivWithinAt
  have hg_bd : ∀ s ∈ Set.Icc t₀ (t₀ + h), ‖V (x s) - V (x t₀)‖ ≤ M * B * h := by
    intro s hs
    calc
      ‖V (x s) - V (x t₀)‖ ≤ M * ‖x s - x t₀‖ := hLip (x s) (x t₀)
      _ ≤ M * (B * h) := mul_le_mul_of_nonneg_left (hx_lip s hs) hM
      _ = M * B * h := by ring
  have hmvt_g := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hg_deriv hg_bd
    (convex_Icc t₀ (t₀ + h)) ht0_mem hth_mem
  have hg0 : g t₀ = 0 := by simp [g]
  have hgh : g (t₀ + h) = x (t₀ + h) - residualStep h V (x t₀) := by
    dsimp [g, residualStep]
    simp only [add_sub_cancel_left]
    abel
  have hhnorm : ‖(t₀ + h) - t₀‖ = h := by
    rw [add_sub_cancel_left, Real.norm_eq_abs, abs_of_nonneg hh]
  rw [hgh, hg0, sub_zero, hhnorm] at hmvt_g
  refine hmvt_g.trans_eq ?_
  ring

/-- **Global `O(1 / L)` Neural ODE Convergence Bound**:
at depth `L ≥ 1`, `‖residualFlow L T V x₀ L - x T‖ ≤ (B * T / L) * exp (M * T)`. -/
theorem residualFlow_global_error_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : E → E) {M B T : ℝ} (hM : 0 < M) (hB : 0 ≤ B) (hT : 0 < T)
    (hLip : ∀ u v : E, ‖V u - V v‖ ≤ M * ‖u - v‖)
    (x₀ : E) (x : ℝ → E) (hx0 : x 0 = x₀)
    (hode : ∀ s ∈ Set.Icc (0 : ℝ) T, HasDerivAt x (V (x s)) s ∧ ‖V (x s)‖ ≤ B)
    (L : ℕ) (hL : 1 ≤ L) :
    ‖residualFlow L T V x₀ L - x T‖ ≤ (B * T / (L : ℝ)) * Real.exp (M * T) := by
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  let h : ℝ := T / (L : ℝ)
  have hh : 0 ≤ h := (div_pos hT hLpos).le
  let e : ℕ → ℝ := fun k => if k ≤ L then ‖residualFlow L T V x₀ k - x ((k : ℝ) * h)‖ else 0
  have he0 : e 0 = 0 := by
    dsimp [e]
    simp [residualFlow, hx0]
  have he_step : ∀ k : ℕ, e (k + 1) ≤ (1 + M * h) * e k + M * B * h ^ 2 := by
    intro k
    by_cases hk1 : k + 1 ≤ L
    · have hkL : k ≤ L := Nat.le_of_succ_le hk1
      have hkL_r : (k : ℝ) ≤ (L : ℝ) := by exact_mod_cast hkL
      have hk1L_r : ((k + 1 : ℕ) : ℝ) ≤ (L : ℝ) := by exact_mod_cast hk1
      dsimp [e]
      rw [if_pos hk1, if_pos hkL]
      let yk := residualFlow L T V x₀ k
      let xk := x ((k : ℝ) * h)
      have hsplit : residualFlow L T V x₀ (k + 1) - x (((k + 1 : ℕ) : ℝ) * h) =
          (residualStep h V yk - residualStep h V xk) +
            (residualStep h V xk - x ((k : ℝ) * h + h)) := by
        dsimp [residualFlow]
        have hstep_t : (((k + 1 : ℕ) : ℝ) * h) = (k : ℝ) * h + h := by
          push_cast
          ring
        rw [hstep_t]
        abel
      have htri :
          ‖residualFlow L T V x₀ (k + 1) - x (((k + 1 : ℕ) : ℝ) * h)‖ ≤
            ‖residualStep h V yk - residualStep h V xk‖ +
              ‖residualStep h V xk - x ((k : ℝ) * h + h)‖ := by
        rw [hsplit]
        exact norm_add_le _ _
      have hdiff_step :
          ‖residualStep h V yk - residualStep h V xk‖ ≤ (1 + M * h) * ‖yk - xk‖ := by
        have hrew : residualStep h V yk - residualStep h V xk =
            (yk - xk) + h • (V yk - V xk) := by
          dsimp [residualStep]
          rw [smul_sub]
          abel
        rw [hrew]
        calc
          ‖(yk - xk) + h • (V yk - V xk)‖ ≤ ‖yk - xk‖ + ‖h • (V yk - V xk)‖ := norm_add_le _ _
          _ = ‖yk - xk‖ + h * ‖V yk - V xk‖ := by
              rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hh]
          _ ≤ ‖yk - xk‖ + h * (M * ‖yk - xk‖) := by
              gcongr
              exact hLip yk xk
          _ = (1 + M * h) * ‖yk - xk‖ := by ring
      have hsub_icc : Set.Icc ((k : ℝ) * h) ((k : ℝ) * h + h) ⊆ Set.Icc (0 : ℝ) T := by
        intro s hs
        constructor
        · have hk0 : 0 ≤ (k : ℝ) * h := mul_nonneg (Nat.cast_nonneg k) hh
          linarith [hs.1]
        · have hup : (k : ℝ) * h + h ≤ T := by
            have hkh : (k : ℝ) * h + h = ((k + 1 : ℕ) : ℝ) * h := by
              push_cast
              ring
            rw [hkh]
            calc
              ((k + 1 : ℕ) : ℝ) * (T / (L : ℝ)) ≤ (L : ℝ) * (T / (L : ℝ)) := by
                exact mul_le_mul_of_nonneg_right hk1L_r hh
              _ = T := mul_div_cancel₀ T hLpos.ne'
          linarith [hs.2]
      have hloc := local_euler_truncation_bound V hM.le hB hh hLip x
        (fun s hs => hode s (hsub_icc hs))
      have hloc' : ‖residualStep h V xk - x ((k : ℝ) * h + h)‖ ≤ M * B * h ^ 2 := by
        rw [norm_sub_rev]
        exact hloc
      exact htri.trans (add_le_add hdiff_step hloc')
    · dsimp [e]
      rw [if_neg hk1]
      have h0 : 0 ≤ (1 + M * h) * (if k ≤ L then ‖residualFlow L T V x₀ k - x ((k : ℝ) * h)‖ else 0) +
          M * B * h ^ 2 := by
        have h1 : 0 ≤ 1 + M * h := by positivity
        have he_nn : 0 ≤ if k ≤ L then ‖residualFlow L T V x₀ k - x ((k : ℝ) * h)‖ else 0 := by
          split_ifs <;> positivity
        have hmb : 0 ≤ M * B * h ^ 2 := by positivity
        exact add_nonneg (mul_nonneg h1 he_nn) hmb
      exact h0
  have ha : 0 ≤ M * h := mul_nonneg hM.le hh
  have hb : 0 ≤ M * B * h ^ 2 := by positivity
  have hgron := discrete_gronwall_bound ha e he0 he_step L
  have hLT : (L : ℝ) * h = T := mul_div_cancel₀ T hLpos.ne'
  have heL : e L = ‖residualFlow L T V x₀ L - x T‖ := by
    dsimp [e]
    rw [if_pos le_rfl, hLT]
  rw [heL] at hgron
  have hexp_pow : (1 + M * h) ^ L ≤ Real.exp (M * T) := by
    have h1 : 1 + M * h ≤ Real.exp (M * h) := by linarith [Real.add_one_le_exp (M * h)]
    have hpow := pow_le_pow_left₀ (by positivity) h1 L
    rw [← Real.exp_nat_mul] at hpow
    have hexp_eq : (L : ℝ) * (M * h) = M * T := by
      calc
        (L : ℝ) * (M * h) = M * ((L : ℝ) * h) := by ring
        _ = M * T := by rw [hLT]
    rwa [hexp_eq] at hpow
  have hsub1 : (1 + M * h) ^ L - 1 ≤ Real.exp (M * T) := by linarith
  have hmb_le : (M * B * h ^ 2) * ((1 + M * h) ^ L - 1) ≤ (M * B * h ^ 2) * Real.exp (M * T) :=
    mul_le_mul_of_nonneg_left hsub1 hb
  have hcomb : (M * h) * ‖residualFlow L T V x₀ L - x T‖ ≤ (M * B * h ^ 2) * Real.exp (M * T) :=
    hgron.trans hmb_le
  have hMh_pos : 0 < M * h := mul_pos hM (div_pos hT hLpos)
  have hdiv := div_le_div_of_nonneg_right hcomb hMh_pos.le
  rw [mul_div_cancel_left₀ _ hMh_pos.ne'] at hdiv
  refine hdiv.trans_eq ?_
  have hM_ne : M ≠ 0 := hM.ne'
  have hL_ne : (L : ℝ) ≠ 0 := hLpos.ne'
  dsimp [h]
  field_simp [hM_ne, hL_ne]

/-- **Continuous-Depth Transformer Neural ODE Limit (`L → ∞`)**:
as the normalized layer count `L → ∞`, `residualFlow L T V x₀ L → x T`. -/
theorem tendsto_residualFlow_continuous_depth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : E → E) {M B T : ℝ} (hM : 0 < M) (hB : 0 ≤ B) (hT : 0 < T)
    (hLip : ∀ u v : E, ‖V u - V v‖ ≤ M * ‖u - v‖)
    (x₀ : E) (x : ℝ → E) (hx0 : x 0 = x₀)
    (hode : ∀ s ∈ Set.Icc (0 : ℝ) T, HasDerivAt x (V (x s)) s ∧ ‖V (x s)‖ ≤ B) :
    Tendsto (fun L : ℕ => residualFlow L T V x₀ L) atTop (𝓝 (x T)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h_upper : Tendsto (fun L : ℕ => (B * T / (L : ℝ)) * Real.exp (M * T)) atTop (𝓝 0) := by
    have hinv : Tendsto (fun L : ℕ => ((L : ℝ)⁻¹)) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    have hmul : Tendsto (fun L : ℕ => (B * T * Real.exp (M * T)) * (L : ℝ)⁻¹) atTop (𝓝 0) := by
      simpa using hinv.const_mul (B * T * Real.exp (M * T))
    refine hmul.congr fun L => ?_
    ring
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_upper
    (Eventually.of_forall fun _ => norm_nonneg _) ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with L hL
  exact residualFlow_global_error_le V hM hB hT hLip x₀ x hx0 hode L hL

/-! ## 2. Continuous-Depth Softmax Attention Consensus Dynamics & Exponential Variance Decay -/

/-- Continuous-depth token-cloud attention vector field `(V_P X)_i = ∑_j P(X)_{ij} (X_j - X_i)`. -/
def attnDrift {N d : ℕ} (P : (Fin N → Fin d → ℝ) → Fin N → Fin N → ℝ)
    (X : Fin N → Fin d → ℝ) (i : Fin N) (c : Fin d) : ℝ :=
  ∑ j : Fin N, P X i j * (X j c - X i c)

/-- Softmax attention transition kernel realized directly via `tempGibbsWeight` from
`KreinPositionalThermodynamicAttention`. -/
def softmaxAttnKernel {N d : ℕ} [NeZero N] (β : ℝ)
    (score : (Fin d → ℝ) → (Fin d → ℝ) → ℝ)
    (X : Fin N → Fin d → ℝ) (i j : Fin N) : ℝ :=
  tempGibbsWeight (fun k => -score (X i) (X k)) β j

theorem softmaxAttnKernel_pos {N d : ℕ} [NeZero N] (β : ℝ)
    (score : (Fin d → ℝ) → (Fin d → ℝ) → ℝ)
    (X : Fin N → Fin d → ℝ) (i j : Fin N) :
    0 < softmaxAttnKernel β score X i j :=
  tempGibbsWeight_pos _ β j

theorem softmaxAttnKernel_row_sum_one {N d : ℕ} [NeZero N] (β : ℝ)
    (score : (Fin d → ℝ) → (Fin d → ℝ) → ℝ)
    (X : Fin N → Fin d → ℝ) (i : Fin N) :
    ∑ j : Fin N, softmaxAttnKernel β score X i j = 1 :=
  tempGibbsWeight_sum_one _ β

/-- Token cloud center of mass along coordinate `c`. -/
def tokenCenterOfMass {N d : ℕ} (X : Fin N → Fin d → ℝ) (c : Fin d) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i : Fin N, X i c

/-- Token cloud quadratic energy `(1/2) ∑_{i,c} X_{ic}^2`. -/
def cloudEnergy {N d : ℕ} (X : Fin N → Fin d → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ i : Fin N, ∑ c : Fin d, (X i c) ^ 2

/-- Token cloud mean-centered variance `(1/2) ∑_{i,c} (X_{ic} - X̄_c)^2`. -/
def cloudVariance {N d : ℕ} (X : Fin N → Fin d → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ i : Fin N, ∑ c : Fin d, (X i c - tokenCenterOfMass X c) ^ 2

/-- **Center-of-Mass Conservation Law**: under any doubly stochastic continuous-depth attention kernel,
every coordinate of `tokenCenterOfMass` has exact zero time derivative. -/
theorem hasDerivAt_centerOfMass_zero_of_doublyStochastic {N d : ℕ}
    (P : (Fin N → Fin d → ℝ) → Fin N → Fin N → ℝ)
    (X : ℝ → Fin N → Fin d → ℝ) {t : ℝ}
    (hode : ∀ i c, HasDerivAt (fun s => X s i c) (attnDrift P (X t) i c) t)
    (hrow : ∀ i, ∑ j : Fin N, P (X t) i j = 1)
    (hcol : ∀ j, ∑ i : Fin N, P (X t) i j = 1)
    (c : Fin d) :
    HasDerivAt (fun s => tokenCenterOfMass (X s) c) 0 t := by
  have hsum : HasDerivAt (fun s => ∑ i : Fin N, X s i c) (∑ i : Fin N, attnDrift P (X t) i c) t :=
    HasDerivAt.fun_sum fun i _ => hode i c
  have hdrift_zero : ∑ i : Fin N, attnDrift P (X t) i c = 0 := by
    dsimp [attnDrift]
    have hexpand :
        (∑ i : Fin N, ∑ j : Fin N, P (X t) i j * (X t j c - X t i c)) =
          (∑ j : Fin N, (∑ i : Fin N, P (X t) i j) * X t j c) -
            (∑ i : Fin N, (∑ j : Fin N, P (X t) i j) * X t i c) := by
      simp_rw [mul_sub, Finset.sum_sub_distrib]
      congr 1
      · rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_mul]
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_mul]
    rw [hexpand]
    simp_rw [hcol, hrow, one_mul, sub_self]
  have hm := hsum.const_mul ((N : ℝ)⁻¹)
  rw [hdrift_zero, mul_zero] at hm
  exact hm

private lemma symm_dirichlet_pairing_identity {N : ℕ}
    (w : Fin N → Fin N → ℝ) (hw : ∀ i j, w i j = w j i) (u : Fin N → ℝ) :
    (∑ i : Fin N, u i * ∑ j : Fin N, w i j * (u j - u i)) =
      -(1 / 2 : ℝ) * ∑ i : Fin N, ∑ j : Fin N, w i j * (u i - u j) ^ 2 := by
  have h1 :
      (∑ i : Fin N, u i * ∑ j : Fin N, w i j * (u j - u i)) =
        ∑ i : Fin N, ∑ j : Fin N, w i j * u i * (u j - u i) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => by ring
  have h2 :
      (∑ i : Fin N, ∑ j : Fin N, w i j * u i * (u j - u i)) =
        ∑ i : Fin N, ∑ j : Fin N, w i j * u j * (u i - u j) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hw j i]
  have hdouble :
      2 * (∑ i : Fin N, u i * ∑ j : Fin N, w i j * (u j - u i)) =
        ∑ i : Fin N, ∑ j : Fin N, (w i j * u i * (u j - u i) + w i j * u j * (u i - u j)) := by
    calc
      2 * (∑ i : Fin N, u i * ∑ j : Fin N, w i j * (u j - u i))
          = (∑ i : Fin N, u i * ∑ j : Fin N, w i j * (u j - u i)) +
              (∑ i : Fin N, u i * ∑ j : Fin N, w i j * (u j - u i)) := two_mul _
      _ = (∑ i : Fin N, ∑ j : Fin N, w i j * u i * (u j - u i)) +
            (∑ i : Fin N, ∑ j : Fin N, w i j * u j * (u i - u j)) :=
            congrArg₂ (· + ·) h1 (h1.trans h2)
      _ = ∑ i : Fin N, ∑ j : Fin N, (w i j * u i * (u j - u i) + w i j * u j * (u i - u j)) := by
            simp_rw [← Finset.sum_add_distrib]
  have hsq :
      (∑ i : Fin N, ∑ j : Fin N, (w i j * u i * (u j - u i) + w i j * u j * (u i - u j))) =
        -(∑ i : Fin N, ∑ j : Fin N, w i j * (u i - u j) ^ 2) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hsq] at hdouble
  linarith

/-- **Dirichlet Energy Dissipation Law** for continuous-depth symmetric attention dynamics:
`d/dt cloudEnergy(X(t)) = -(1/2) ∑_{i,j} P(X(t))_{ij} ‖X_i(t) - X_j(t)‖²`. -/
theorem hasDerivAt_cloudEnergy_eq_neg_dirichlet {N d : ℕ}
    (P : (Fin N → Fin d → ℝ) → Fin N → Fin N → ℝ)
    (X : ℝ → Fin N → Fin d → ℝ) {t : ℝ}
    (hode : ∀ i c, HasDerivAt (fun s => X s i c) (attnDrift P (X t) i c) t)
    (hsym : ∀ i j, P (X t) i j = P (X t) j i) :
    HasDerivAt (fun s => cloudEnergy (X s))
      (-(1 / 2 : ℝ) * ∑ i : Fin N, ∑ j : Fin N, P (X t) i j *
        ∑ c : Fin d, (X t i c - X t j c) ^ 2) t := by
  have hterm : ∀ i c,
      HasDerivAt (fun s => (X s i c) ^ 2) (2 * X t i c * attnDrift P (X t) i c) t := by
    intro i c
    have hd := (hode i c).pow 2
    refine hd.congr_deriv ?_
    ring
  have hsum :
      HasDerivAt (fun s => ∑ i : Fin N, ∑ c : Fin d, (X s i c) ^ 2)
        (∑ i : Fin N, ∑ c : Fin d, 2 * X t i c * attnDrift P (X t) i c) t :=
    HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun c _ => hterm i c
  have hhalf := hsum.const_mul (1 / 2 : ℝ)
  refine hhalf.congr_deriv ?_
  have hsimp :
      (1 / 2 : ℝ) * ∑ i : Fin N, ∑ c : Fin d, 2 * X t i c * attnDrift P (X t) i c =
        ∑ c : Fin d, ∑ i : Fin N, X t i c * ∑ j : Fin N, P (X t) i j * (X t j c - X t i c) := by
    rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    dsimp [attnDrift]
    ring
  rw [hsimp]
  have hdir :
      (∑ c : Fin d, ∑ i : Fin N, X t i c * ∑ j : Fin N, P (X t) i j * (X t j c - X t i c)) =
        ∑ c : Fin d, -(1 / 2 : ℝ) * ∑ i : Fin N, ∑ j : Fin N,
          P (X t) i j * (X t i c - X t j c) ^ 2 := by
    refine Finset.sum_congr rfl fun c _ => ?_
    exact symm_dirichlet_pairing_identity (P (X t)) hsym (fun i => X t i c)
  rw [hdir, ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.mul_sum]

/-- **Mean-Centered Variance Dissipation Law** for continuous-depth symmetric row-stochastic attention. -/
theorem hasDerivAt_cloudVariance_eq_neg_dirichlet {N d : ℕ}
    (P : (Fin N → Fin d → ℝ) → Fin N → Fin N → ℝ)
    (X : ℝ → Fin N → Fin d → ℝ) {t : ℝ}
    (hode : ∀ i c, HasDerivAt (fun s => X s i c) (attnDrift P (X t) i c) t)
    (hsym : ∀ i j, P (X t) i j = P (X t) j i)
    (hrow : ∀ i, ∑ j : Fin N, P (X t) i j = 1) :
    HasDerivAt (fun s => cloudVariance (X s))
      (-(1 / 2 : ℝ) * ∑ i : Fin N, ∑ j : Fin N, P (X t) i j *
        ∑ c : Fin d, (X t i c - X t j c) ^ 2) t := by
  have hcol : ∀ j, ∑ i : Fin N, P (X t) i j = 1 := fun j => by
    calc
      ∑ i : Fin N, P (X t) i j = ∑ i : Fin N, P (X t) j i :=
        Finset.sum_congr rfl fun i _ => hsym i j
      _ = 1 := hrow j
  have hbar : ∀ c, HasDerivAt (fun s => tokenCenterOfMass (X s) c) 0 t := fun c =>
    hasDerivAt_centerOfMass_zero_of_doublyStochastic P X hode hrow hcol c
  have hterm : ∀ i c,
      HasDerivAt (fun s => (X s i c - tokenCenterOfMass (X s) c) ^ 2)
        (2 * (X t i c - tokenCenterOfMass (X t) c) * attnDrift P (X t) i c) t := by
    intro i c
    have hd := ((hode i c).sub (hbar c)).pow 2
    refine hd.congr_deriv ?_
    simp [sub_zero, pow_one, mul_assoc]
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) fun i _ =>
    HasDerivAt.fun_sum (u := Finset.univ) fun c _ => hterm i c
  have hhalf := hsum.const_mul (1 / 2 : ℝ)
  refine hhalf.congr_deriv ?_
  have hbar_drift : ∀ c, ∑ i : Fin N, tokenCenterOfMass (X t) c * attnDrift P (X t) i c = 0 := by
    intro c
    rw [← Finset.mul_sum]
    have hdz : ∑ i : Fin N, attnDrift P (X t) i c = 0 := by
      dsimp [attnDrift]
      have hexp :
          (∑ i : Fin N, ∑ j : Fin N, P (X t) i j * (X t j c - X t i c)) =
            (∑ j : Fin N, (∑ i : Fin N, P (X t) i j) * X t j c) -
              (∑ i : Fin N, (∑ j : Fin N, P (X t) i j) * X t i c) := by
        simp_rw [mul_sub, Finset.sum_sub_distrib]
        congr 1
        · rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_mul]
        · refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_mul]
      rw [hexp]
      simp_rw [hcol, hrow, one_mul, sub_self]
    rw [hdz, mul_zero]
  have heq_deriv :
      (1 / 2 : ℝ) * ∑ i : Fin N, ∑ c : Fin d,
          2 * (X t i c - tokenCenterOfMass (X t) c) * attnDrift P (X t) i c =
        ∑ c : Fin d, ∑ i : Fin N, X t i c * ∑ j : Fin N, P (X t) i j * (X t j c - X t i c) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    have hsplit :
        (∑ i : Fin N, (1 / 2 : ℝ) * (2 * (X t i c - tokenCenterOfMass (X t) c) * attnDrift P (X t) i c)) =
          (∑ i : Fin N, X t i c * attnDrift P (X t) i c) -
            (∑ i : Fin N, tokenCenterOfMass (X t) c * attnDrift P (X t) i c) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => by ring
    rw [hsplit, hbar_drift c, sub_zero]
    simp only [attnDrift]
    simp_rw [Finset.mul_sum]
  rw [heq_deriv]
  have hdir :
      (∑ c : Fin d, ∑ i : Fin N, X t i c * ∑ j : Fin N, P (X t) i j * (X t j c - X t i c)) =
        ∑ c : Fin d, -(1 / 2 : ℝ) * ∑ i : Fin N, ∑ j : Fin N,
          P (X t) i j * (X t i c - X t j c) ^ 2 := by
    refine Finset.sum_congr rfl fun c _ => ?_
    exact symm_dirichlet_pairing_identity (P (X t)) hsym (fun i => X t i c)
  rw [hdir, ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.mul_sum]

private lemma sum_pairwise_sq_eq_two_N_variance {N : ℕ} [NeZero N] (u : Fin N → ℝ) :
    ∑ i : Fin N, ∑ j : Fin N, (u i - u j) ^ 2 =
      2 * (N : ℝ) * ∑ i : Fin N, (u i - ((N : ℝ)⁻¹ * ∑ k : Fin N, u k)) ^ 2 := by
  let ubar : ℝ := (N : ℝ)⁻¹ * ∑ k : Fin N, u k
  have hNpos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  have hNne : (N : ℝ) ≠ 0 := hNpos.ne'
  have hsum_u : ∑ k : Fin N, u k = (N : ℝ) * ubar := by
    dsimp [ubar]
    rw [← mul_assoc, mul_inv_cancel₀ hNne, one_mul]
  have hlhs :
      ∑ i : Fin N, ∑ j : Fin N, (u i - u j) ^ 2 =
        2 * (N : ℝ) * (∑ i : Fin N, u i ^ 2) - 2 * (∑ i : Fin N, u i) ^ 2 := by
    have hexp : ∀ i j : Fin N, (u i - u j) ^ 2 = u i ^ 2 - 2 * u i * u j + u j ^ 2 :=
      fun i j => by ring
    simp_rw [hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hinner1 : (∑ i : Fin N, ∑ j : Fin N, 2 * u i * u j) = 2 * (∑ i : Fin N, u i) ^ 2 := by
      have h1 : ∀ i : Fin N, (∑ j : Fin N, 2 * u i * u j) = (2 * u i) * ∑ j : Fin N, u j :=
        fun i => by rw [← Finset.mul_sum]
      simp_rw [h1, ← Finset.sum_mul, ← Finset.mul_sum]
      ring
    rw [hinner1]
    simp_rw [← Finset.mul_sum]
    ring
  have hrhs :
      2 * (N : ℝ) * ∑ i : Fin N, (u i - ubar) ^ 2 =
        2 * (N : ℝ) * (∑ i : Fin N, u i ^ 2) - 2 * (∑ i : Fin N, u i) ^ 2 := by
    have hexp : ∀ i : Fin N, (u i - ubar) ^ 2 = u i ^ 2 - 2 * ubar * u i + ubar ^ 2 :=
      fun i => by ring
    simp_rw [hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [hsum_u]
    ring
  exact hlhs.trans hrhs.symm

/-- Doeblin-lower-bounded symmetric attention satisfies the sharp differential inequality
`(cloudVariance ∘ X)'(t) ≤ -2 * N * δ * cloudVariance(X(t))`. -/
theorem hasDerivAt_cloudVariance_le_exp_rate {N d : ℕ} [NeZero N]
    (P : (Fin N → Fin d → ℝ) → Fin N → Fin N → ℝ)
    (X : ℝ → Fin N → Fin d → ℝ) {t δ : ℝ}
    (hode : ∀ i c, HasDerivAt (fun s => X s i c) (attnDrift P (X t) i c) t)
    (hsym : ∀ i j, P (X t) i j = P (X t) j i)
    (hrow : ∀ i, ∑ j : Fin N, P (X t) i j = 1)
    (hdoeblin : ∀ i j, δ ≤ P (X t) i j) :
    HasDerivAt (fun s => cloudVariance (X s))
      (-(1 / 2 : ℝ) * ∑ i : Fin N, ∑ j : Fin N, P (X t) i j *
        ∑ c : Fin d, (X t i c - X t j c) ^ 2) t ∧
    (-(1 / 2 : ℝ) * ∑ i : Fin N, ∑ j : Fin N, P (X t) i j *
      ∑ c : Fin d, (X t i c - X t j c) ^ 2) ≤ -2 * (N : ℝ) * δ * cloudVariance (X t) := by
  refine ⟨hasDerivAt_cloudVariance_eq_neg_dirichlet P X hode hsym hrow, ?_⟩
  have hlow :
      δ * ∑ i : Fin N, ∑ j : Fin N, ∑ c : Fin d, (X t i c - X t j c) ^ 2 ≤
        ∑ i : Fin N, ∑ j : Fin N, P (X t) i j * ∑ c : Fin d, (X t i c - X t j c) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    exact mul_le_mul_of_nonneg_right (hdoeblin i j)
      (Finset.sum_nonneg fun c _ => sq_nonneg _)
  have hid :
      ∑ i : Fin N, ∑ j : Fin N, ∑ c : Fin d, (X t i c - X t j c) ^ 2 =
        4 * (N : ℝ) * cloudVariance (X t) := by
    have hswap :
        (∑ i : Fin N, ∑ j : Fin N, ∑ c : Fin d, (X t i c - X t j c) ^ 2) =
          ∑ c : Fin d, ∑ i : Fin N, ∑ j : Fin N, (X t i c - X t j c) ^ 2 := by
      calc
        (∑ i : Fin N, ∑ j : Fin N, ∑ c : Fin d, (X t i c - X t j c) ^ 2)
            = ∑ i : Fin N, ∑ c : Fin d, ∑ j : Fin N, (X t i c - X t j c) ^ 2 :=
                Finset.sum_congr rfl fun i _ => Finset.sum_comm
        _ = ∑ c : Fin d, ∑ i : Fin N, ∑ j : Fin N, (X t i c - X t j c) ^ 2 :=
              Finset.sum_comm
    rw [hswap]
    have hpair :
        (∑ c : Fin d, ∑ i : Fin N, ∑ j : Fin N, (X t i c - X t j c) ^ 2) =
          ∑ c : Fin d, 2 * (N : ℝ) * ∑ i : Fin N, (X t i c - tokenCenterOfMass (X t) c) ^ 2 :=
      Finset.sum_congr rfl fun c _ => sum_pairwise_sq_eq_two_N_variance (fun i => X t i c)
    rw [hpair, ← Finset.mul_sum]
    dsimp [cloudVariance]
    rw [Finset.sum_comm]
    ring
  rw [hid] at hlow
  nlinarith

/-- **Exponential Consensus Collapse (`exp (-2 N δ t)`)**:
for any uniform positive Doeblin coupling `δ > 0`, `cloudVariance (X t) ≤ cloudVariance (X 0) * exp(-2 N δ t)`
and `cloudVariance (X t) → 0` as `t → ∞`. -/
theorem cloudVariance_le_exp_decay {N d : ℕ} [NeZero N]
    (P : (Fin N → Fin d → ℝ) → Fin N → Fin N → ℝ)
    (X : ℝ → Fin N → Fin d → ℝ) {δ : ℝ}
    (hode : ∀ t ≥ 0, ∀ i c, HasDerivAt (fun s => X s i c) (attnDrift P (X t) i c) t)
    (hsym : ∀ t ≥ 0, ∀ i j, P (X t) i j = P (X t) j i)
    (hrow : ∀ t ≥ 0, ∀ i, ∑ j : Fin N, P (X t) i j = 1)
    (hdoeblin : ∀ t ≥ 0, ∀ i j, δ ≤ P (X t) i j) :
    ∀ t ≥ 0, cloudVariance (X t) ≤ cloudVariance (X 0) * Real.exp (-2 * (N : ℝ) * δ * t) := by
  let c : ℝ := 2 * (N : ℝ) * δ
  let g : ℝ → ℝ := fun s => cloudVariance (X s) * Real.exp (c * s)
  have hg_deriv : ∀ s ≥ 0, ∃ g', HasDerivAt g g' s ∧ g' ≤ 0 := by
    intro s hs
    have hrate := hasDerivAt_cloudVariance_le_exp_rate P X (hode s hs) (hsym s hs)
      (hrow s hs) (hdoeblin s hs)
    have hexp : HasDerivAt (fun u => Real.exp (c * u)) (c * Real.exp (c * s)) s := by
      have hlin : HasDerivAt (fun u => c * u) c s := by
        simpa using (hasDerivAt_id s).const_mul c
      simpa [mul_comm] using hlin.exp
    refine ⟨_, hrate.1.mul hexp, ?_⟩
    have hexp_pos : 0 < Real.exp (c * s) := Real.exp_pos _
    have hcomb :
        (-(1 / 2 : ℝ) * ∑ i : Fin N, ∑ j : Fin N, P (X s) i j *
            ∑ k : Fin d, (X s i k - X s j k) ^ 2) + c * cloudVariance (X s) ≤ 0 := by
      dsimp [c]
      linarith [hrate.2]
    calc
      (-(1 / 2 : ℝ) * ∑ i : Fin N, ∑ j : Fin N, P (X s) i j *
          ∑ k : Fin d, (X s i k - X s j k) ^ 2) * Real.exp (c * s) +
          cloudVariance (X s) * (c * Real.exp (c * s))
          = ((-(1 / 2 : ℝ) * ∑ i : Fin N, ∑ j : Fin N, P (X s) i j *
              ∑ k : Fin d, (X s i k - X s j k) ^ 2) + c * cloudVariance (X s)) *
            Real.exp (c * s) := by ring
      _ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hcomb hexp_pos.le
  let g' : ℝ → ℝ := fun s => if hs : 0 ≤ s then (hg_deriv s hs).choose else 0
  have hg_cont : ContinuousOn g (Set.Ici 0) := fun s hs =>
    ((hg_deriv s hs).choose_spec.1.continuousAt).continuousWithinAt
  have hg_anti : AntitoneOn g (Set.Ici 0) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := g') (convex_Ici 0) hg_cont ?_ ?_
    · intro s hs
      have hs0 : 0 ≤ s := Set.mem_Ici.mp (interior_subset hs)
      dsimp [g']
      simp only [hs0, ↓reduceDIte]
      exact (hg_deriv s hs0).choose_spec.1.hasDerivWithinAt
    · intro s hs
      have hs0 : 0 ≤ s := Set.mem_Ici.mp (interior_subset hs)
      dsimp [g']
      simp only [hs0, ↓reduceDIte]
      exact (hg_deriv s hs0).choose_spec.2
  intro t ht
  have hle : g t ≤ g 0 := hg_anti (by simp) ht ht
  dsimp [g, c] at hle
  simp only [mul_zero, Real.exp_zero, mul_one] at hle
  have hexp_pos : 0 < Real.exp (2 * (N : ℝ) * δ * t) := Real.exp_pos _
  have hdiv := div_le_div_of_nonneg_right hle hexp_pos.le
  rw [mul_div_cancel_right₀ _ hexp_pos.ne'] at hdiv
  refine hdiv.trans_eq ?_
  rw [div_eq_mul_inv, ← Real.exp_neg]
  ring_nf

theorem cloudVariance_tendsto_zero {N d : ℕ} [NeZero N]
    (P : (Fin N → Fin d → ℝ) → Fin N → Fin N → ℝ)
    (X : ℝ → Fin N → Fin d → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hode : ∀ t ≥ 0, ∀ i c, HasDerivAt (fun s => X s i c) (attnDrift P (X t) i c) t)
    (hsym : ∀ t ≥ 0, ∀ i j, P (X t) i j = P (X t) j i)
    (hrow : ∀ t ≥ 0, ∀ i, ∑ j : Fin N, P (X t) i j = 1)
    (hdoeblin : ∀ t ≥ 0, ∀ i j, δ ≤ P (X t) i j) :
    Tendsto (fun t : ℝ => cloudVariance (X t)) atTop (𝓝 0) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  have hc_pos : 0 < 2 * (N : ℝ) * δ := mul_pos (mul_pos two_pos hNpos) hδ
  have h_upper :
      Tendsto (fun t : ℝ => cloudVariance (X 0) * Real.exp (-2 * (N : ℝ) * δ * t)) atTop (𝓝 0) := by
    have hmul : Tendsto (fun t : ℝ => (-2 * (N : ℝ) * δ) * t) atTop atBot := by
      refine Tendsto.const_mul_atTop_of_neg ?_ tendsto_id
      linarith [hc_pos]
    have hexp : Tendsto (fun t : ℝ => Real.exp ((-2 * (N : ℝ) * δ) * t)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp hmul
    simpa [mul_assoc] using hexp.const_mul (cloudVariance (X 0))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_upper ?_ ?_
  · exact Eventually.of_forall fun t => by
      dsimp [cloudVariance]
      positivity
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact cloudVariance_le_exp_decay P X hode hsym hrow hdoeblin t ht

end InfoGeometry.LLM.ContinuousDepthTransformerScalingLimit
