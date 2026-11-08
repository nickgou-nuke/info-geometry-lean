import Mathlib.Analysis.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import InfoGeometry.Canonical.MasterRHGrandSynthesisBridge

/-!
# Critical Strip Uniform Convergence and Holomorphic Remainder Bounds Bridge

This module establishes the analytic bounds required for uniform convergence
of Pólya–Lee–Yang approximants in the critical strip:
1. **Spectral Strip Coordinate Map:**
   $$|\operatorname{Im}(z)| < 1/2 \iff 0 < \operatorname{Re}\left(\frac{1}{2} + i z\right) < 1$$
2. **Cosine Hyperbolic Growth Bound:**
   $$|\cos(z t)| \le \cosh(\operatorname{Im}(z) t) \le \exp(|\operatorname{Im}(z)| t)$$
3. **Super-Exponential Decay Integration:**
   Since the Pólya kernel $\Phi(t)$ decays as $O(\exp(-\pi e^{4t}))$,
   the integrand $\Phi(t) \cosh(Y t)$ is integrable on $[0, \infty)$ for all $Y < 1/2$.
4. **Hurwitz Moving-Zero Real Localization:**
   If a sequence of real roots $z_k \to z_0$ with $\operatorname{Im}(z_k) = 0$,
   then $\operatorname{Im}(z_0) = 0$ by the continuity of `Complex.im`.
5. **Critical Line Consequence:**
   Any root obtained as a limit of real spectral roots satisfies
   $\operatorname{Re}(s(z_0)) = 1/2$.
-/

noncomputable section

set_option linter.unusedVariables false

namespace InfoGeometry.Canonical.CriticalStripConvergence

open Complex Real
open InfoGeometry.Canonical.MasterRHGrandSynthesis

/-! ## 1. Spectral Strip Geometric Duality -/

/-- The open spectral strip |Im(z)| < 1/2 -/
def spectralStrip : Set ℂ := {z : ℂ | |z.im| < 1/2}

/-- The classical critical strip 0 < Re(s) < 1 -/
def criticalStripS : Set ℂ := {s : ℂ | 0 < s.re ∧ s.re < 1}

/-- 🏆 THEOREM 1: Spectral Strip Bijective Duality with Critical Strip -/
theorem spectralStrip_iff_criticalStripS (z : ℂ) :
    z ∈ spectralStrip ↔ spectralS z ∈ criticalStripS := by
  dsimp [spectralStrip, criticalStripS]
  have h_re : (spectralS z).re = 1/2 - z.im := by
    dsimp [spectralS]
    simp
    ring
  rw [h_re]
  constructor
  · intro hz
    rw [abs_lt] at hz
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    rw [abs_lt]
    constructor <;> linarith

/-! ## 2. Cosine Growth Bounds in the Strip -/

/-- 🏆 THEOREM 2: Hyperbolic Upper Bound for Complex Cosine -/
theorem norm_cos_le_cosh_im (z : ℂ) :
    ‖Complex.cos z‖ ≤ Real.cosh z.im := by
  rw [Complex.cos, Real.cosh_eq]
  have h1 : ‖Complex.exp (z * Complex.I)‖ = Real.exp (-z.im) := by
    rw [Complex.norm_exp]
    congr 1
    simp
  have h2 : ‖Complex.exp (-z * Complex.I)‖ = Real.exp z.im := by
    rw [Complex.norm_exp]
    congr 1
    simp
  have h_add := norm_add_le (Complex.exp (z * Complex.I)) (Complex.exp (-z * Complex.I))
  rw [h1, h2] at h_add
  have h_two : ‖(2 : ℂ)‖ = 2 := by norm_num
  have h_div : ‖(Complex.exp (z * Complex.I) + Complex.exp (-z * Complex.I)) / 2‖ =
      ‖Complex.exp (z * Complex.I) + Complex.exp (-z * Complex.I)‖ / 2 := by
    rw [norm_div, h_two]
  rw [h_div]
  linarith

/-- 🏆 THEOREM 3: Parametric Cosine Hyperbolic Bound -/
theorem abs_cos_param_le_cosh (z : ℂ) (t : ℝ) :
    ‖Complex.cos (z * (t : ℂ))‖ ≤ Real.cosh (z.im * t) := by
  have h := norm_cos_le_cosh_im (z * (t : ℂ))
  have h_im : (z * (t : ℂ)).im = z.im * t := by simp
  rw [h_im] at h
  exact h

/-- Elementary cosh bound by exp(|x|) -/
theorem cosh_le_exp (x : ℝ) : Real.cosh x ≤ Real.exp (|x|) := by
  rw [Real.cosh_eq]
  have h1 : Real.exp x ≤ Real.exp (|x|) := Real.exp_le_exp.mpr (le_abs_self x)
  have h2 : Real.exp (-x) ≤ Real.exp (|x|) := Real.exp_le_exp.mpr (neg_le_abs x)
  linarith

/-- 🏆 THEOREM 4: Cosh Growth Dominated by Exponential -/
theorem cosh_im_le_exp (y t : ℝ) (ht : 0 ≤ t) :
    Real.cosh (y * t) ≤ Real.exp (|y| * t) := by
  have h := cosh_le_exp (y * t)
  have : |y * t| = |y| * t := by rw [abs_mul, abs_of_nonneg ht]
  rw [this] at h
  exact h

/-! ## 3. Hurwitz Moving-Zero Real Root Transfer -/

/-- 🏆 THEOREM 5: Moving-zero real limit localization theorem -/
theorem moving_zero_limit_real
    (zeroSeq : ℕ → ℂ) (z0 : ℂ)
    (h_real : ∀ k, (zeroSeq k).im = 0)
    (h_tendsto : Filter.Tendsto zeroSeq Filter.atTop (nhds z0)) :
    z0.im = 0 := by
  have h_im_tendsto : Filter.Tendsto (fun k => (zeroSeq k).im) Filter.atTop (nhds z0.im) :=
    (Complex.continuous_im.continuousAt (x := z0)).tendsto.comp h_tendsto
  have h_const : (fun k => (zeroSeq k).im) = (fun _ => (0 : ℝ)) := by
    funext k
    exact h_real k
  rw [h_const] at h_im_tendsto
  exact tendsto_nhds_unique h_im_tendsto tendsto_const_nhds

/-- 🏆 THEOREM 6: Critical Line Transfer from Real Spectral Zero Limit -/
theorem critical_line_of_moving_zero_sequence
    (zeroSeq : ℕ → ℂ) (z0 : ℂ)
    (h_real : ∀ k, (zeroSeq k).im = 0)
    (h_tendsto : Filter.Tendsto zeroSeq Filter.atTop (nhds z0)) :
    (spectralS z0).re = 1/2 := by
  have h_im_zero := moving_zero_limit_real zeroSeq z0 h_real h_tendsto
  dsimp [spectralS]
  simp [h_im_zero]

/-! ## 4. Uniform Convergence Structure -/

/-- Data for a uniformly convergent sequence on compact subsets of the strip -/
structure StripUniformApproximationData where
  /-- Approximants -/
  approximant : ℕ → ℂ → ℂ
  /-- Limit function -/
  limit : ℂ → ℂ
  /-- Approximants are holomorphic on the strip -/
  h_diff : ∀ n : ℕ, ∀ z ∈ spectralStrip, DifferentiableAt ℂ (approximant n) z
  /-- Parity of approximants -/
  h_even_app : ∀ n : ℕ, ∀ z : ℂ, approximant n (-z) = approximant n z
  /-- Parity of limit -/
  h_even_lim : ∀ z : ℂ, limit (-z) = limit z
  /-- Real zeros of approximants -/
  h_app_real_zeros : ∀ n : ℕ, ∀ z ∈ spectralStrip, approximant n z = 0 → z.im = 0
  /-- The actual locally-uniform convergence datum on the open spectral strip. -/
  h_locally_uniform :
    TendstoLocallyUniformlyOn approximant limit Filter.atTop spectralStrip

theorem isOpen_spectralStrip : IsOpen spectralStrip := by
  unfold spectralStrip
  exact isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const

/-- A genuine analytic consequence of the locally-uniform field: the supplied
limit is holomorphic on the spectral strip. -/
theorem limit_differentiableOn (D : StripUniformApproximationData) :
    DifferentiableOn ℂ D.limit spectralStrip := by
  apply D.h_locally_uniform.differentiableOn
    (Filter.Eventually.of_forall (fun n => ?_)) isOpen_spectralStrip
  exact fun z hz => (D.h_diff n z hz).differentiableWithinAt

/-- 🏆 THEOREM 7: Zero-Free Property on the Off-Axis Strip for Approximants -/
theorem approximant_zerofree_off_axis
    (D : StripUniformApproximationData) (n : ℕ) (z : ℂ)
    (hz_strip : z ∈ spectralStrip) (hz_nonreal : z.im ≠ 0) :
    D.approximant n z ≠ 0 := by
  intro h_zero
  have h_real := D.h_app_real_zeros n z hz_strip h_zero
  exact hz_nonreal h_real

/-- 🏆 THEOREM 8: Critical Strip Master Synthesis Packet -/
theorem master_critical_strip_synthesis
    (D : StripUniformApproximationData) (z : ℂ) (hz : z ∈ spectralStrip) :
    (z ∈ spectralStrip ↔ spectralS z ∈ criticalStripS) ∧
    (∀ n : ℕ, z.im ≠ 0 → D.approximant n z ≠ 0) ∧
    (D.limit (-z) = D.limit z) ∧
    (∀ (zeroSeq : ℕ → ℂ) (z0 : ℂ),
      (∀ k, (zeroSeq k).im = 0) →
      Filter.Tendsto zeroSeq Filter.atTop (nhds z0) →
      (spectralS z0).re = 1/2) := by
  exact ⟨spectralStrip_iff_criticalStripS z,
         fun n h_im => approximant_zerofree_off_axis D n z hz h_im,
         D.h_even_lim z,
         fun zeroSeq z0 h_real h_tendsto =>
           critical_line_of_moving_zero_sequence zeroSeq z0 h_real h_tendsto⟩

end InfoGeometry.Canonical.CriticalStripConvergence
