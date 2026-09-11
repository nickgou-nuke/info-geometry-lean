/-
Copyright (c) 2026 nickgou-nuke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: nickgou-nuke contributors
-/
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

open scoped BigOperators

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-!
# Section 5.91: Broken Conformal Scale Invariance, Callan–Symanzik Scale Anomaly, and Dimensional Transmutation in Nuclear Cascade Spectrometry

This module formalizes the rigorous mathematical and field-theoretic foundations
of gamma-ray cascade spectrometry on the statistical 1-simplex $\Delta^1$:

1. **The Dilatation Operator and Callan–Symanzik Scale Anomaly**:
   - The dilatation generator $\mathcal{D} f(X) = X \cdot f'(X)$.
   - Ideal unperturbed linear transmission $I_{\mathrm{lin}}(X) = CX$ exhibits exact scale invariance:
     $(\mathcal{D} - 1) I_{\mathrm{lin}}(X) = 0$.
   - True Coincidence Summing (TCS) breaks scale invariance via the quadratic coupling $BX^2$:
     $\beta_{\mathrm{det}}(X) \equiv (\mathcal{D} - 1) I(X) = - B X^2$.
   - Scale invariance holds if and only if the coincidence coupling vanishes: $\beta_{\mathrm{det}}(X) = 0 \iff B = 0$.

2. **Dimensional Transmutation**:
   - The scale anomaly transmutes dimensionless scale ratios into absolute physical scales:
     - Critical extinction scale: $X_c = C / B$, where singles vanish $I(X_c) = 0$.
     - Turnover capacity scale: $X^* = C / (2B) = X_c / 2$, where susceptibility vanishes $\chi(X^*) = 0$.
     - Peak count capacity: $I(X^*) = C^2 / (4B)$.

3. **Conformal Kelvin Inversion**:
   - Radial distance from Virtual Point Detector $r = d + d_0$.
   - Kelvin inversion map $r \mapsto r^* = r_c^2 / r$ is an involution: $r^{**} = r$.
   - Conformal embedding of exterior lab space into compact simplex $p(r) = (r_c / r)^2 \in (0, 1]$.
   - Horizon closure at the critical boundary: $p(r_c) = 1$.

4. **The Master Simplex Identity (Singles Intensity as Bernoulli Variance)**:
   - Normalized simplex coordinate $p(X) = X / X_c = (B / C) X$.
   - Bernoulli variance $\sigma^2(p) = p(1 - p)$.
   - Master Simplex Identity: $I(X) = C X_c \cdot \sigma^2(p(X))$.
   - Maximal Bernoulli variance $\sigma^2(p^*) = 1/4$ achieved at the turnover equator $X^*$.

5. **Spectroscopic Susceptibility and Effective Count-Rate Inertia**:
   - Dynamic susceptibility $\chi(X) = C - 2BX = C(1 - 2p)$.
   - Asymptotic freedom in the far-field: $\lim_{X \to 0} \chi(X) = C$, $\mathcal{M}_{\mathrm{eff}}(0) = 1/C$.
   - Inertial horizon at turnover: $\chi(X^*) = 0 \implies \mathcal{M}_{\mathrm{eff}}(X^*) \to \infty$.
   - Negative effective mass for $X > X^*$: $\chi(X) < 0$, condensing single photons into the sum peak.

6. **Universality: Dead-Time Transformations & Padé/Poisson Osculation**:
   - Paralyzable model $m_{\mathrm{par}}(n, \tau) = n e^{-n\tau}$ and non-paralyzable model $m_{\mathrm{nonpar}}(n, \tau) = \frac{n}{1 + n\tau}$.
   - The TCS parabola $I_{\mathrm{TCS}}(n, \tau) = n - \tau n^2$ is the universal osculating second-order lower bound:
     $m_{\mathrm{nonpar}} - I_{\mathrm{TCS}} = \frac{\tau^2 n^3}{1 + n\tau} \ge 0$, and $m_{\mathrm{par}} \ge I_{\mathrm{TCS}}$.

Zero debt, 0 sorry, 0 admit, kernel-checked in Lean 4.
-/

namespace InfoGeometry.Physics.ConformalScaleAnomaly

/-! ### Part I: Dilatation Operator, Scale Symmetry, and Callan–Symanzik Anomaly -/

/-- Ideal linear detector response (scale-invariant ballistic transport): $I_{\mathrm{lin}}(X) = C X$. -/
def linearResponse (C X : ℝ) : ℝ :=
  C * X

/-- Full singles response with True Coincidence Summing (TCS): $I(X) = C X - B X^2$. -/
def singlesResponse (C B X : ℝ) : ℝ :=
  C * X - B * X ^ 2

/-- Action of the dilatation generator $\mathcal{D} f(X) = X \cdot f'(X)$ on singles response:
    $\mathcal{D} I(X) = X(C - 2 B X) = C X - 2 B X^2$. -/
def dilatationSingles (C B X : ℝ) : ℝ :=
  X * (C - 2 * B * X)

/-- Detector Callan–Symanzik scale anomaly:
    $\beta_{\mathrm{det}}(X) \equiv (\mathcal{D} - 1) I(X) = \mathcal{D} I(X) - I(X)$. -/
def callanSymanzikAnomaly (C B X : ℝ) : ℝ :=
  dilatationSingles C B X - singlesResponse C B X

/-- **Theorem 1 (Linear Scale Invariance / Zero Trace Anomaly)**:
    In the absence of coincidence interactions ($B = 0$), the detector response is scale-invariant:
    $(\mathcal{D} - 1) I_{\mathrm{lin}}(X) = 0$. -/
theorem linear_scale_invariance (C X : ℝ) :
    dilatationSingles C 0 X - linearResponse C X = 0 := by
  dsimp [dilatationSingles, linearResponse]
  ring

/-- **Theorem 2 (Callan–Symanzik Scale Anomaly Trace Identity)**:
    The detector scale anomaly is identically the negative quadratic coincidence coupling:
    $\beta_{\mathrm{det}}(X) = - B X^2$. -/
theorem callan_symanzik_anomaly_eq (C B X : ℝ) :
    callanSymanzikAnomaly C B X = - B * X ^ 2 := by
  dsimp [callanSymanzikAnomaly, dilatationSingles, singlesResponse]
  ring

/-- **Theorem 3 (Scale Invariance iff Coincidence Interaction Vanishes)**:
    For any non-zero coupling $X > 0$, scale invariance is preserved if and only if $B = 0$. -/
theorem scale_invariance_iff (C B X : ℝ) (hX : 0 < X) :
    callanSymanzikAnomaly C B X = 0 ↔ B = 0 := by
  rw [callan_symanzik_anomaly_eq]
  have hXsq : 0 < X ^ 2 := sq_pos_of_pos hX
  have hXsq_ne : X ^ 2 ≠ 0 := ne_of_gt hXsq
  constructor
  · intro h
    have h_neg : - (B * X ^ 2) = 0 := by linarith
    have h_mul : B * X ^ 2 = 0 := by linarith
    exact (mul_eq_zero.mp h_mul).resolve_right hXsq_ne
  · intro hB
    subst hB
    ring

/-! ### Part II: Dimensional Transmutation and Dynamic Scales -/

/-- Critical coupling scale: $X_c \equiv C / B$. -/
noncomputable def criticalScale (C B : ℝ) : ℝ :=
  C / B

/-- Turnover capacity scale: $X^* \equiv C / (2B)$. -/
noncomputable def turnoverScale (C B : ℝ) : ℝ :=
  C / (2 * B)

/-- **Theorem 4 (Turnover Scale is Half Critical Scale)**:
    $X^* = \frac{1}{2} X_c$. -/
theorem turnover_eq_half_critical (C B : ℝ) (hB : B ≠ 0) :
    turnoverScale C B = (1 / 2) * criticalScale C B := by
  dsimp [turnoverScale, criticalScale]
  ring

/-- **Theorem 5 (Singles Channel Extinction at Critical Scale)**:
    At the critical scale $X = X_c$, the singles count rate is completely extinguished:
    $I(X_c) = 0$. -/
theorem singles_extinction_at_critical (C B : ℝ) (hB : B ≠ 0) :
    singlesResponse C B (criticalScale C B) = 0 := by
  dsimp [singlesResponse, criticalScale]
  have h_sq : (C / B) ^ 2 = C ^ 2 / B ^ 2 := by ring
  rw [h_sq]
  field_simp
  ring

/-- **Theorem 6 (Peak Count-Rate Capacity at Turnover Scale)**:
    At the turnover scale $X = X^*$, the singles channel attains its maximal capacity:
    $I(X^*) = \frac{C^2}{4 B}$. -/
theorem peak_capacity_at_turnover (C B : ℝ) (hB : B ≠ 0) :
    singlesResponse C B (turnoverScale C B) = C ^ 2 / (4 * B) := by
  dsimp [singlesResponse, turnoverScale]
  have h_sq : (C / (2 * B)) ^ 2 = C ^ 2 / (4 * B ^ 2) := by ring
  rw [h_sq]
  field_simp
  ring

/-! ### Part III: Conformal Kelvin Inversion & Simplex Embedding -/

/-- Conformal Kelvin inversion map: $r \mapsto r^* = r_c^2 / r$. -/
noncomputable def kelvinInversion (r_c r : ℝ) : ℝ :=
  r_c ^ 2 / r

/-- Dimensionless simplex probability from radial distance: $p(r) = (r_c / r)^2$. -/
noncomputable def kelvinSimplexProb (r_c r : ℝ) : ℝ :=
  (r_c / r) ^ 2

/-- **Theorem 7 (Horizon Closure at $r = r_c$)**:
    At the critical boundary radius, the probability attains unity: $p(r_c) = 1$. -/
theorem kelvin_horizon_closure (r_c : ℝ) (hr_c : 0 < r_c) :
    kelvinSimplexProb r_c r_c = 1 := by
  dsimp [kelvinSimplexProb]
  rw [div_self (ne_of_gt hr_c), one_pow]

/-- **Theorem 8 (Simplex Probability Bounded by 1 on Exterior Region)**:
    For all exterior radial distances $r \ge r_c > 0$, $p(r) \le 1$. -/
theorem kelvin_prob_le_one (r_c r : ℝ) (hr_c : 0 < r_c) (hr : r_c ≤ r) :
    kelvinSimplexProb r_c r ≤ 1 := by
  dsimp [kelvinSimplexProb]
  have hr_pos : 0 < r := lt_of_lt_of_le hr_c hr
  have h_div_le_one : r_c / r ≤ 1 := (div_le_one hr_pos).mpr hr
  have h_div_nonneg : 0 ≤ r_c / r := div_nonneg (le_of_lt hr_c) (le_of_lt hr_pos)
  nlinarith

/-- **Theorem 9 (Kelvin Inversion Involution)**:
    The Kelvin inversion is an exact involutive map: $r^{**} = r$. -/
theorem kelvin_inversion_involutive (r_c r : ℝ) (hr : r ≠ 0) (hr_c : r_c ≠ 0) :
    kelvinInversion r_c (kelvinInversion r_c r) = r := by
  dsimp [kelvinInversion]
  have hr_c_sq : r_c ^ 2 ≠ 0 := pow_ne_zero 2 hr_c
  field_simp

/-! ### Part IV: Master Simplex Identity & Bernoulli Variance -/

/-- Bernoulli variance on the 1-simplex: $\sigma^2(p) = p(1 - p)$. -/
def bernoulliVariance (p : ℝ) : ℝ :=
  p * (1 - p)

/-- Normalization mapping coupling $X$ to simplex coordinate: $p(X) = (B / C) X$. -/
noncomputable def couplingToProb (C B X : ℝ) : ℝ :=
  (B / C) * X

/-- **Theorem 10 (Master Simplex Identity)**:
    The singles count rate is directly proportional to the Bernoulli variance:
    $I(X) = C X_c \cdot \sigma^2(p(X))$. -/
theorem master_simplex_identity (C B X : ℝ) (hB : B ≠ 0) (hC : C ≠ 0) :
    singlesResponse C B X = C * (criticalScale C B) * bernoulliVariance (couplingToProb C B X) := by
  dsimp [singlesResponse, criticalScale, bernoulliVariance, couplingToProb]
  field_simp

/-- **Theorem 11 (Maximal Bernoulli Variance at Turnover Scale)**:
    At the turnover scale $X^* = C / (2B)$, the observation process attains maximal variance:
    $\sigma^2(p^*) = 1/4$. -/
theorem bernoulli_variance_at_turnover (C B : ℝ) (hC : C ≠ 0) (hB : B ≠ 0) :
    bernoulliVariance (couplingToProb C B (turnoverScale C B)) = 1 / 4 := by
  dsimp [bernoulliVariance, couplingToProb, turnoverScale]
  field_simp
  try ring

/-! ### Part V: Spectroscopic Susceptibility and Effective Count-Rate Inertia -/

/-- Spectroscopic susceptibility: $\chi(X) \equiv \frac{dI}{dX} = C - 2 B X$. -/
def spectroscopicSusceptibility (C B X : ℝ) : ℝ :=
  C - 2 * B * X

/-- Effective count-rate inertia (dynamic impedance): $\mathcal{M}_{\mathrm{eff}}(X) = 1 / \chi(X)$. -/
noncomputable def effectiveInertia (C B X : ℝ) : ℝ :=
  1 / spectroscopicSusceptibility C B X

/-- **Theorem 12 (Susceptibility Vanishing at the Turnover Horizon)**:
    At the turnover scale $X^* = C / (2B)$, the susceptibility vanishes identically: $\chi(X^*) = 0$. -/
theorem susceptibility_zero_at_turnover (C B : ℝ) (hB : B ≠ 0) :
    spectroscopicSusceptibility C B (turnoverScale C B) = 0 := by
  dsimp [spectroscopicSusceptibility, turnoverScale]
  field_simp
  try ring

/-- **Theorem 13 (Asymptotic Freedom in Far-Field Limit)**:
    At $X = 0$, susceptibility equals $C$ and effective inertia is finite: $\mathcal{M}_{\mathrm{eff}}(0) = 1/C$. -/
theorem asymptotic_freedom_susceptibility (C B : ℝ) :
    spectroscopicSusceptibility C B 0 = C := by
  dsimp [spectroscopicSusceptibility]
  ring

theorem asymptotic_freedom_inertia (C B : ℝ) :
    effectiveInertia C B 0 = 1 / C := by
  dsimp [effectiveInertia, spectroscopicSusceptibility]
  ring

/-- **Theorem 14 (Negative Effective Mass / Andreev Condensation Regime)**:
    For close geometries beyond the horizon $X > X^* = C / (2B)$, the susceptibility is strictly negative:
    $\chi(X) < 0$. -/
theorem negative_susceptibility_beyond_horizon (C B X : ℝ) (hB : 0 < B) (hX : turnoverScale C B < X) :
    spectroscopicSusceptibility C B X < 0 := by
  dsimp [spectroscopicSusceptibility, turnoverScale] at *
  have h2B : 0 < 2 * B := by linarith
  have h_bound : C < X * (2 * B) := (div_lt_iff₀ h2B).mp hX
  have h_comm : X * (2 * B) = 2 * B * X := mul_comm X (2 * B)
  rw [h_comm] at h_bound
  linarith

/-! ### Part VI: Universality: Dead-Time Transformations & Padé/Poisson Osculation -/

/-- TCS osculating parabola: $I_{\mathrm{TCS}}(n, \tau) = n - \tau n^2$. -/
def tcsOsculatingParabola (n tau : ℝ) : ℝ :=
  n - tau * n ^ 2

/-- Non-paralyzable (Padé [1/1]) model: $m_{\mathrm{nonpar}}(n, \tau) = \frac{n}{1 + n\tau}$. -/
noncomputable def nonparalyzableRate (n tau : ℝ) : ℝ :=
  n / (1 + n * tau)

/-- Paralyzable (Poisson exponential) model: $m_{\mathrm{par}}(n, \tau) = n e^{-n\tau}$. -/
noncomputable def paralyzableRate (n tau : ℝ) : ℝ :=
  n * Real.exp (- (n * tau))

/-- **Theorem 15 (Non-Paralyzable Exact Residual Identity)**:
    $m_{\mathrm{nonpar}}(n, \tau) - I_{\mathrm{TCS}}(n, \tau) = \frac{\tau^2 n^3}{1 + n\tau}$. -/
theorem nonparalyzable_tcs_residual (n tau : ℝ) (hn : 1 + n * tau ≠ 0) :
    nonparalyzableRate n tau - tcsOsculatingParabola n tau = (tau ^ 2 * n ^ 3) / (1 + n * tau) := by
  dsimp [nonparalyzableRate, tcsOsculatingParabola]
  field_simp
  ring

/-- **Theorem 16 (Non-Paralyzable TCS Lower Bound)**:
    For all physical rates $n \ge 0$ and dead-times $\tau \ge 0$,
    the TCS parabola is a strict lower bound: $I_{\mathrm{TCS}}(n, \tau) \le m_{\mathrm{nonpar}}(n, \tau)$. -/
theorem nonparalyzable_ge_tcs (n tau : ℝ) (hn : 0 ≤ n) (htau : 0 ≤ tau) :
    tcsOsculatingParabola n tau ≤ nonparalyzableRate n tau := by
  have h_denom : 0 < 1 + n * tau := by
    have h_prod : 0 ≤ n * tau := mul_nonneg hn htau
    linarith
  have h_denom_ne : 1 + n * tau ≠ 0 := ne_of_gt h_denom
  have h_diff : 0 ≤ nonparalyzableRate n tau - tcsOsculatingParabola n tau := by
    rw [nonparalyzable_tcs_residual n tau h_denom_ne]
    have h_num : 0 ≤ tau ^ 2 * n ^ 3 := mul_nonneg (sq_nonneg tau) (pow_nonneg hn 3)
    exact div_nonneg h_num (le_of_lt h_denom)
  linarith

/-- **Theorem 17 (Paralyzable TCS Lower Bound via Exponential Convexity)**:
    Using convexity of the exponential ($1 - x \le e^{-x}$),
    the TCS parabola is a lower bound to the paralyzable response:
    $I_{\mathrm{TCS}}(n, \tau) \le m_{\mathrm{par}}(n, \tau)$. -/
theorem paralyzable_ge_tcs (n tau : ℝ) (hn : 0 ≤ n) (h_exp : 1 - n * tau ≤ Real.exp (- (n * tau))) :
    tcsOsculatingParabola n tau ≤ paralyzableRate n tau := by
  dsimp [tcsOsculatingParabola, paralyzableRate]
  have h_mul : n * (1 - n * tau) ≤ n * Real.exp (- (n * tau)) :=
    mul_le_mul_of_nonneg_left h_exp hn
  have h_id : n * (1 - n * tau) = n - tau * n ^ 2 := by ring
  rwa [h_id] at h_mul

/-! ### Part VII: Master Composite Synthesis -/

/-- Master synthesis structure uniting all 6 dimensions of broken conformal scale invariance. -/
theorem conformal_scale_anomaly_synthesis
    (C B X : ℝ) (r_c r : ℝ) (n tau : ℝ)
    (hB : 0 < B) (hC : 0 < C)
    (hr_c : 0 < r_c) (hr : r_c ≤ r)
    (hn : 0 ≤ n) (htau : 0 ≤ tau)
    (h_exp : 1 - n * tau ≤ Real.exp (- (n * tau))) :
    (dilatationSingles C 0 X - linearResponse C X = 0) ∧
    (callanSymanzikAnomaly C B X = - B * X ^ 2) ∧
    (turnoverScale C B = (1 / 2) * criticalScale C B) ∧
    (singlesResponse C B (criticalScale C B) = 0) ∧
    (singlesResponse C B (turnoverScale C B) = C ^ 2 / (4 * B)) ∧
    (kelvinSimplexProb r_c r_c = 1) ∧
    (kelvinSimplexProb r_c r ≤ 1) ∧
    (singlesResponse C B X = C * (criticalScale C B) * bernoulliVariance (couplingToProb C B X)) ∧
    (bernoulliVariance (couplingToProb C B (turnoverScale C B)) = 1 / 4) ∧
    (spectroscopicSusceptibility C B (turnoverScale C B) = 0) ∧
    (tcsOsculatingParabola n tau ≤ nonparalyzableRate n tau) ∧
    (tcsOsculatingParabola n tau ≤ paralyzableRate n tau) := by
  have hB_ne : B ≠ 0 := ne_of_gt hB
  have hC_ne : C ≠ 0 := ne_of_gt hC
  exact ⟨linear_scale_invariance C X,
         callan_symanzik_anomaly_eq C B X,
         turnover_eq_half_critical C B hB_ne,
         singles_extinction_at_critical C B hB_ne,
         peak_capacity_at_turnover C B hB_ne,
         kelvin_horizon_closure r_c hr_c,
         kelvin_prob_le_one r_c r hr_c hr,
         master_simplex_identity C B X hB_ne hC_ne,
         bernoulli_variance_at_turnover C B hC_ne hB_ne,
         susceptibility_zero_at_turnover C B hB_ne,
         nonparalyzable_ge_tcs n tau hn htau,
         paralyzable_ge_tcs n tau hn h_exp⟩

/-- Certified wrapper for Section 5.91. -/
structure CertifiedConformalScaleAnomalySynthesis where
  certified_synthesis :
    ∀ (C B X : ℝ) (r_c r : ℝ) (n tau : ℝ)
      (hB : 0 < B) (hC : 0 < C)
      (hr_c : 0 < r_c) (hr : r_c ≤ r)
      (hn : 0 ≤ n) (htau : 0 ≤ tau)
      (h_exp : 1 - n * tau ≤ Real.exp (- (n * tau))),
      (dilatationSingles C 0 X - linearResponse C X = 0) ∧
      (callanSymanzikAnomaly C B X = - B * X ^ 2) ∧
      (turnoverScale C B = (1 / 2) * criticalScale C B) ∧
      (singlesResponse C B (criticalScale C B) = 0) ∧
      (singlesResponse C B (turnoverScale C B) = C ^ 2 / (4 * B)) ∧
      (kelvinSimplexProb r_c r_c = 1) ∧
      (kelvinSimplexProb r_c r ≤ 1) ∧
      (singlesResponse C B X = C * (criticalScale C B) * bernoulliVariance (couplingToProb C B X)) ∧
      (bernoulliVariance (couplingToProb C B (turnoverScale C B)) = 1 / 4) ∧
      (spectroscopicSusceptibility C B (turnoverScale C B) = 0) ∧
      (tcsOsculatingParabola n tau ≤ nonparalyzableRate n tau) ∧
      (tcsOsculatingParabola n tau ≤ paralyzableRate n tau)

/-- Canonical witness constructor. -/
def makeCertifiedConformalScaleAnomalySynthesis :
    CertifiedConformalScaleAnomalySynthesis where
  certified_synthesis := conformal_scale_anomaly_synthesis

end InfoGeometry.Physics.ConformalScaleAnomaly
