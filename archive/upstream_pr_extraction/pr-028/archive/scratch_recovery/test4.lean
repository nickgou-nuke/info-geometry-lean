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

def denomSq (g : SL2R) (τ : InfoGeometry.Geometry.RealUpperHalfPlane) : ℝ :=
  (c g * τ.x + d g) ^ 2 + (c g * τ.y) ^ 2

def moebius (g : SL2R) (τ : InfoGeometry.Geometry.RealUpperHalfPlane) : InfoGeometry.Geometry.RealUpperHalfPlane :=
  { x :=
      ((a g * τ.x + b g) * (c g * τ.x + d g) + a g * c g * τ.y ^ 2) /
        denomSq g τ
    y := τ.y / denomSq g τ
    y_pos := sorry }

def toComplex (τ : InfoGeometry.Geometry.RealUpperHalfPlane) : ℍ :=
  ⟨Complex.mk τ.x τ.y, by simpa using τ.y_pos⟩

theorem toComplex_moebius (g : SL2R) (τ : InfoGeometry.Geometry.RealUpperHalfPlane) :
    toComplex (moebius g τ) = g • toComplex τ := by
  let z := toComplex τ
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  set a' := a g
  set b' := b g
  set c' := c g
  set d' := d g
  have hdet : a' * d' - b' * c' = 1 := sorry
  have hpos : denomSq g τ > 0 := sorry
  apply Complex.ext
  · dsimp [toComplex, moebius, a, b, c, d, denomSq]
    simp only [Complex.div_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.normSq, mul_zero, add_zero, zero_mul, sub_zero, zero_add]
    ring
  · dsimp [toComplex, moebius, a, b, c, d, denomSq]
    simp only [Complex.div_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.normSq, mul_zero, add_zero, zero_mul, sub_zero, zero_add]
    have : (-(a' * τ.x + b') * (c' * τ.y) + a' * τ.y * (c' * τ.x + d')) = τ.y * (a' * d' - b' * c') := by ring
    rw [this, hdet, mul_one]
