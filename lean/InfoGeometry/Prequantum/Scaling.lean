import Mathlib

/-- Minimal prequantum line-bundle data (scalarized): symplectic scale `ω`,
curvature scale `F`, and conversion constant `ℏ` with relation `F = ω / ℏ`. -/
structure PrequantumData where
  omegaScale : ℝ
  curvatureScale : ℝ
  hbar : ℝ
  hbar_ne_zero : hbar ≠ 0
  curvature_law : curvatureScale = omegaScale / hbar

theorem PrequantumData.curvature_mul_hbar_eq_omega
    (P : PrequantumData) :
    P.curvatureScale * P.hbar = P.omegaScale := by
  rw [P.curvature_law]
  field_simp [P.hbar_ne_zero]

theorem PrequantumData.omega_eq_hbar_mul_curvature
    (P : PrequantumData) :
    P.omegaScale = P.hbar * P.curvatureScale := by
  have h := P.curvature_mul_hbar_eq_omega
  linarith

/-- Rescaling `ℏ` by `c` rescales curvature by `1/c` at fixed symplectic scale. -/
noncomputable def PrequantumData.rescaleHbar
    (P : PrequantumData) (c : ℝ) (hc : c ≠ 0) : PrequantumData where
  omegaScale := P.omegaScale
  curvatureScale := P.curvatureScale / c
  hbar := c * P.hbar
  hbar_ne_zero := mul_ne_zero hc P.hbar_ne_zero
  curvature_law := by
    rw [P.curvature_law]
    field_simp [hc, P.hbar_ne_zero]

theorem PrequantumData.rescaleHbar_curvature
    (P : PrequantumData) (c : ℝ) (hc : c ≠ 0) :
    (P.rescaleHbar c hc).curvatureScale = P.curvatureScale / c := rfl

theorem PrequantumData.rescaleHbar_hbar
    (P : PrequantumData) (c : ℝ) (hc : c ≠ 0) :
    (P.rescaleHbar c hc).hbar = c * P.hbar := rfl
