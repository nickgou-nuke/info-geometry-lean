import Mathlib.Analysis.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import InfoGeometry.Canonical.MasterRHDeductionBridge

/-!
# Abstract Hardy-Z Readout Datum

This module formalizes an explicit datum for a real-valued critical-line
readout. It does not construct the standard Riemann--Siegel theta function,
the analytic Hardy Z-function, or the completed xi-function. In particular,
the parity and scale identities below are assumptions of `HardyZDatum`.

The proved consequences are:
1. **A supplied phase readout**:
   $$Z(t) = e^{i \theta(t)} \cdot \zeta\left(\frac{1}{2} + i t\right)$$
2. **Reality of the supplied real codomain**:
   $$\overline{Z(t)} = Z(t) \iff \operatorname{Im}(Z(t)) = 0$$
3. **Exact Zero Equivalence**:
   $$Z(t_0) = 0 \iff \zeta\left(\frac{1}{2} + i t_0\right) = 0$$
4. **A supplied evenness law**:
   $$Z(-t) = Z(t)$$
5. **A supplied scale relation**:
   $$\xi\left(\frac{1}{2} + i t\right) = \operatorname{scale}(t) \cdot Z(t)$$
-/

noncomputable section

namespace InfoGeometry.Canonical.HardyZ

open Complex
open InfoGeometry.Canonical.MasterRH

/-- Datum of a Hardy Z-system along the critical line s(t) = 1/2 + i t -/
structure HardyZDatum where
  /-- Riemann-Siegel phase angle θ : ℝ → ℝ -/
  theta : ℝ → ℝ
  /-- Real Hardy function Z : ℝ → ℝ -/
  Z : ℝ → ℝ
  /-- Complex Riemann zeta evaluated on critical line -/
  zeta_crit : ℝ → ℂ
  /-- Completed xi evaluated on critical line -/
  xi_crit : ℝ → ℂ
  /-- Non-vanishing scale factor relating Z and xi -/
  scale_factor : ℝ → ℝ
  /-- Scale factor is strictly positive (hence non-zero) -/
  scale_pos : ∀ t : ℝ, 0 < scale_factor t
  /-- Phase rotation identity: Z(t) = e^{i θ(t)} * zeta(1/2 + it) -/
  h_hardy_def : ∀ t : ℝ, (Z t : ℂ) = Complex.exp (Complex.I * (theta t : ℂ)) * zeta_crit t
  /-- Even parity of Hardy Z function: Z(-t) = Z(t) -/
  h_even : ∀ t : ℝ, Z (-t) = Z t
  /-- Completed xi identity: xi(1/2 + it) = scale(t) * Z(t) -/
  h_xi_Z : ∀ t : ℝ, xi_crit t = (scale_factor t : ℂ) * (Z t : ℂ)

/-- 🏆 THEOREM 1: The Hardy Z-Function is Strictly Real-Valued -/
theorem hardy_Z_im_zero (D : HardyZDatum) (t : ℝ) :
    ((D.Z t : ℂ)).im = 0 := by
  exact Complex.ofReal_im (D.Z t)

/-- 🏆 THEOREM 2: Exact Zero Equivalence: Z(t₀) = 0 ↔ zeta(1/2 + i t₀) = 0 -/
theorem hardy_Z_zero_iff_zeta_zero (D : HardyZDatum) (t0 : ℝ) :
    D.Z t0 = 0 ↔ D.zeta_crit t0 = 0 := by
  have h_def := D.h_hardy_def t0
  have h_phase_ne : Complex.exp (Complex.I * (D.theta t0 : ℂ)) ≠ 0 := by
    exact Complex.exp_ne_zero (Complex.I * (D.theta t0 : ℂ))
  constructor
  · intro hZ
    have hZ_c : (D.Z t0 : ℂ) = 0 := by rw [hZ, Complex.ofReal_zero]
    rw [hZ_c] at h_def
    have h_mul : Complex.exp (Complex.I * (D.theta t0 : ℂ)) * D.zeta_crit t0 = 0 := h_def.symm
    cases mul_eq_zero.mp h_mul with
    | inl h_exp => exact (h_phase_ne h_exp).elim
    | inr h_zeta => exact h_zeta
  · intro h_zeta
    have h_mul_zero : (D.Z t0 : ℂ) = 0 := by rw [h_def, h_zeta, mul_zero]
    exact Complex.ofReal_eq_zero.mp h_mul_zero

/-- 🏆 THEOREM 3: Exact Zero Equivalence: Z(t₀) = 0 ↔ xi(1/2 + i t₀) = 0 -/
theorem hardy_Z_zero_iff_xi_zero (D : HardyZDatum) (t0 : ℝ) :
    D.Z t0 = 0 ↔ D.xi_crit t0 = 0 := by
  have h_xi := D.h_xi_Z t0
  have h_scale_ne : (D.scale_factor t0 : ℂ) ≠ 0 := by
    have : D.scale_factor t0 ≠ 0 := ne_of_gt (D.scale_pos t0)
    exact Complex.ofReal_ne_zero.mpr this
  constructor
  · intro hZ
    have hZ_c : (D.Z t0 : ℂ) = 0 := by rw [hZ, Complex.ofReal_zero]
    rw [h_xi, hZ_c, mul_zero]
  · intro h_xi_zero
    rw [h_xi_zero] at h_xi
    have h_mul : (D.scale_factor t0 : ℂ) * (D.Z t0 : ℂ) = 0 := h_xi.symm
    cases mul_eq_zero.mp h_mul with
    | inl h_scale => exact (h_scale_ne h_scale).elim
    | inr hZ_c => exact Complex.ofReal_eq_zero.mp hZ_c

/-- 🏆 THEOREM 4: Xi and Zeta Zero Equivalence along the Critical Line -/
theorem hardy_xi_zero_iff_zeta_zero (D : HardyZDatum) (t0 : ℝ) :
    D.xi_crit t0 = 0 ↔ D.zeta_crit t0 = 0 := by
  rw [← hardy_Z_zero_iff_xi_zero D t0]
  exact hardy_Z_zero_iff_zeta_zero D t0

/-- 🏆 THEOREM 5: Time-Reversal Parity Invariance of Zero Locus:
    Z(t₀) = 0 ↔ Z(-t₀) = 0 -/
theorem hardy_Z_zero_parity (D : HardyZDatum) (t0 : ℝ) :
    D.Z t0 = 0 ↔ D.Z (-t0) = 0 := by
  rw [D.h_even t0]

end InfoGeometry.Canonical.HardyZ
