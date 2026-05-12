import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import InfoGeometry.Geometry.RealUpperHalfPlane

open scoped MatrixGroups
open UpperHalfPlane

abbrev SL2R : Type := SL(2, ℝ)

def a (g : SL2R) : ℝ := g.1 0 0
def b (g : SL2R) : ℝ := g.1 0 1
def c (g : SL2R) : ℝ := g.1 1 0
def d (g : SL2R) : ℝ := g.1 1 1

noncomputable def denomSq (g : SL2R) (τ : InfoGeometry.Geometry.RealUpperHalfPlane) : ℝ :=
  (c g * τ.x + d g) ^ 2 + (c g * τ.y) ^ 2

lemma denomSq_pos (g : SL2R) (τ : InfoGeometry.Geometry.RealUpperHalfPlane) : 0 < denomSq g τ := by
  dsimp [denomSq]
  have h_y_pos := τ.y_pos
  by_cases hc : c g = 0
  · rw [hc, zero_mul, zero_add, zero_mul, zero_pow (by norm_num), add_zero]
    have hdet := g.det_coe
    have : a g * d g - b g * c g = 1 := by
      rw [← Matrix.det_fin_two]
      exact hdet
    rw [hc, mul_zero, sub_zero] at this
    have hd_ne_zero : d g ≠ 0 := by
      intro h
      rw [h, mul_zero] at this
      norm_num at this
    exact pow_two_pos_of_ne_zero _ hd_ne_zero
  · have h1 : 0 ≤ (c g * τ.x + d g) ^ 2 := pow_two_nonneg _
    have h2 : 0 < (c g * τ.y) ^ 2 := by
      apply pow_two_pos_of_ne_zero
      apply mul_ne_zero hc h_y_pos.ne.symm
    linarith

noncomputable def moebius (g : SL2R) (τ : InfoGeometry.Geometry.RealUpperHalfPlane) : InfoGeometry.Geometry.RealUpperHalfPlane :=
  { x :=
      ((a g * τ.x + b g) * (c g * τ.x + d g) + a g * c g * τ.y ^ 2) /
        denomSq g τ
    y := τ.y / denomSq g τ
    y_pos := by
      apply div_pos τ.y_pos (denomSq_pos g τ) }

def toComplex (τ : InfoGeometry.Geometry.RealUpperHalfPlane) : ℍ :=
  ⟨Complex.mk τ.x τ.y, by simpa using τ.y_pos⟩

theorem SL2R_det (g : SL2R) : a g * d g - b g * c g = 1 := by
  have h := g.det_coe
  rw [← Matrix.det_fin_two]
  exact h

theorem toComplex_moebius (g : SL2R) (τ : InfoGeometry.Geometry.RealUpperHalfPlane) :
    toComplex (moebius g τ) = g • toComplex τ := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  set a' := a g
  set b' := b g
  set c' := c g
  set d' := d g
  have hdet : a' * d' - b' * c' = 1 := SL2R_det g
  have hpos : denomSq g τ > 0 := denomSq_pos g τ
  apply Complex.ext
  · dsimp [toComplex, moebius, a, b, c, d, denomSq]
    simp only [Complex.div_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.normSq, mul_zero, add_zero, zero_mul, sub_zero, zero_add]
    field_simp [hpos.ne.symm]
    ring
  · dsimp [toComplex, moebius, a, b, c, d, denomSq]
    simp only [Complex.div_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.normSq, mul_zero, add_zero, zero_mul, sub_zero, zero_add]
    field_simp [hpos.ne.symm]
    have : (-(a' * τ.x + b') * (c' * τ.y) + a' * τ.y * (c' * τ.x + d')) = τ.y * (a' * d' - b' * c') := by ring
    rw [this, hdet, mul_one]
