import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-- Minimal prequantum line-bundle data (scalarized): symplectic scale `ω`,
curvature scale `F`, and conversion constant `ℏ` with relation `F = ω / ℏ`. -/
structure PrequantumData where
  omegaScale : ℝ
  curvatureScale : ℝ
  hbar : ℝ
  hbar_ne_zero : hbar ≠ 0
  curvature_law : curvatureScale = omegaScale / hbar

@[ext] theorem PrequantumData.ext
    {P Q : PrequantumData}
    (hOmega : P.omegaScale = Q.omegaScale)
    (hCurv : P.curvatureScale = Q.curvatureScale)
    (hHbar : P.hbar = Q.hbar) :
    P = Q := by
  cases P
  cases Q
  cases hOmega
  cases hCurv
  cases hHbar
  simp

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

theorem PrequantumData.rescaleHbar_rescaleHbar
    (P : PrequantumData) (c d : ℝ) (hc : c ≠ 0) (hd : d ≠ 0) :
    (P.rescaleHbar c hc).rescaleHbar d hd
      = P.rescaleHbar (d * c) (mul_ne_zero hd hc) := by
  ext <;> simp [PrequantumData.rescaleHbar, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

noncomputable instance : SMul (Units ℝ) PrequantumData :=
  ⟨fun u P => P.rescaleHbar (u : ℝ) (Units.ne_zero u)⟩

@[simp] theorem PrequantumData.smul_omegaScale
    (u : Units ℝ) (P : PrequantumData) :
    (u • P).omegaScale = P.omegaScale := rfl

@[simp] theorem PrequantumData.smul_curvatureScale
    (u : Units ℝ) (P : PrequantumData) :
    (u • P).curvatureScale = P.curvatureScale / (u : ℝ) := rfl

@[simp] theorem PrequantumData.smul_hbar
    (u : Units ℝ) (P : PrequantumData) :
    (u • P).hbar = (u : ℝ) * P.hbar := rfl

noncomputable instance : MulAction (Units ℝ) PrequantumData where
  one_smul := by
    intro P
    apply PrequantumData.ext <;> simp
  mul_smul := by
    intro u v P
    symm
    simpa [mul_assoc] using
      (P.rescaleHbar_rescaleHbar
        (c := (v : ℝ)) (d := (u : ℝ))
        (hc := Units.ne_zero v) (hd := Units.ne_zero u))
