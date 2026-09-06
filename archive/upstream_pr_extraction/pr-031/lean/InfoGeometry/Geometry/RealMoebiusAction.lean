/-
InfoGeometry/Geometry/RealMoebiusAction.lean

Pure real fractional-linear action on the real upper half-plane.

This file establishes the identity between the real fractional-linear
transformation and Mathlib's complex-backed modular group action.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Tactic
import InfoGeometry.Geometry.RealUpperHalfPlane

noncomputable section

open scoped MatrixGroups
open UpperHalfPlane

namespace InfoGeometry.Geometry

abbrev SL2R : Type := SL(2, ℝ)
abbrev SL2Z : Type := SL(2, ℤ)

namespace RealUpperHalfPlane

def a (g : SL2R) : ℝ := g.1 0 0
def b (g : SL2R) : ℝ := g.1 0 1
def c (g : SL2R) : ℝ := g.1 1 0
def d (g : SL2R) : ℝ := g.1 1 1

def denomSq (g : SL2R) (τ : RealUpperHalfPlane) : ℝ :=
  (c g * τ.x + d g) ^ 2 + (c g * τ.y) ^ 2
theorem realDenomSq_pos (g : SL2R) (τ : RealUpperHalfPlane) :
    0 < denomSq g τ := by
  unfold denomSq c d
  by_cases hc : g.1 1 0 = 0
  · rw [hc]
    have hdet : g.1 0 0 * g.1 1 1 = 1 := by
      have hdet' := Matrix.SpecialLinearGroup.det_coe g
      rw [Matrix.det_fin_two] at hdet'
      simp [hc] at hdet'
      exact hdet'
    have hdne : g.1 1 1 ≠ 0 := by
      intro hd
      have hzero : g.1 0 0 * g.1 1 1 = 0 := by
        rw [hd, mul_zero]
      rw [hzero] at hdet
      exact zero_ne_one hdet
    have hsq : 0 < (g.1 1 1) ^ 2 := sq_pos_of_ne_zero hdne
    simpa [hc] using hsq
  · have hcy : 0 < (g.1 1 0 * τ.y) ^ 2 := by
      exact sq_pos_of_ne_zero (mul_ne_zero hc τ.y_pos.ne')
    exact add_pos_of_nonneg_of_pos (sq_nonneg _) hcy

def moebius (g : SL2R) (τ : RealUpperHalfPlane) : RealUpperHalfPlane :=
  { x :=
      ((a g * τ.x + b g) * (c g * τ.x + d g) + a g * c g * τ.y ^ 2) /
        denomSq g τ
    y := τ.y / denomSq g τ
    y_pos := by
      exact div_pos τ.y_pos (realDenomSq_pos g τ) }

@[simp]
theorem moebius_x (g : SL2R) (τ : RealUpperHalfPlane) :
    (moebius g τ).x =
      ((a g * τ.x + b g) * (c g * τ.x + d g) + a g * c g * τ.y ^ 2) /
        denomSq g τ := rfl

@[simp]
theorem moebius_y (g : SL2R) (τ : RealUpperHalfPlane) :
    (moebius g τ).y = τ.y / denomSq g τ := rfl

theorem one_moebius (τ : RealUpperHalfPlane) :
    moebius (1 : SL2R) τ = τ := by
  ext
  · simp [moebius, a, b, c, d, denomSq]
  · simp [moebius, a, b, c, d, denomSq]

@[simp]
theorem moebius_y_pos (g : SL2R) (τ : RealUpperHalfPlane) :
    0 < (moebius g τ).y := by
  simpa [moebius] using div_pos τ.y_pos (realDenomSq_pos g τ)

/-- Helper to lift a real point to Mathlib's complex UHP. -/
def toComplex (τ : RealUpperHalfPlane) : ℍ :=
  ⟨Complex.mk τ.x τ.y, by exact τ.y_pos⟩

private lemma real_moebius_re_algebra
    (a b c d x y : ℝ) :
    ((a * x + b) * (c * x + d) + a * c * y ^ 2) /
        ((c * x + d) ^ 2 + (c * y) ^ 2)
      =
    ((((a : ℂ) * ({ re := x, im := y } : ℂ) + (b : ℂ)) /
        ((c : ℂ) * ({ re := x, im := y } : ℂ) + (d : ℂ))).re) := by
  symm
  calc
    ((((a : ℂ) * ({ re := x, im := y } : ℂ) + (b : ℂ)) /
        ((c : ℂ) * ({ re := x, im := y } : ℂ) + (d : ℂ))).re)
        =
      ((a * x + b) * (c * x + d) + (a * y) * (c * y)) /
        ((c * x + d) ^ 2 + (c * y) ^ 2) := by
          simp [Complex.div_re, Complex.normSq]
          ring_nf
    _ =
      ((a * x + b) * (c * x + d) + a * c * y ^ 2) /
        ((c * x + d) ^ 2 + (c * y) ^ 2) := by
          ring_nf

private lemma real_moebius_im_algebra
    (a b c d x y : ℝ) (hdet : a * d - b * c = 1) :
    y / ((c * x + d) ^ 2 + (c * y) ^ 2)
      =
    ((((a : ℂ) * ({ re := x, im := y } : ℂ) + (b : ℂ)) /
        ((c : ℂ) * ({ re := x, im := y } : ℂ) + (d : ℂ))).im) := by
  symm
  calc
    ((((a : ℂ) * ({ re := x, im := y } : ℂ) + (b : ℂ)) /
        ((c : ℂ) * ({ re := x, im := y } : ℂ) + (d : ℂ))).im)
        =
      ((a * y) * (c * x + d) - (a * x + b) * (c * y)) /
        ((c * x + d) ^ 2 + (c * y) ^ 2) := by
          simp [Complex.div_im, Complex.normSq]
          ring_nf
    _ =
      y * (a * d - b * c) /
        ((c * x + d) ^ 2 + (c * y) ^ 2) := by
          ring_nf
    _ =
      y / ((c * x + d) ^ 2 + (c * y) ^ 2) := by
          rw [hdet]
          ring_nf

/-- The real Möbius action is a shadow of the complex one. -/
theorem toComplex_moebius (g : SL2R) (τ : RealUpperHalfPlane) :
    toComplex (moebius g τ) = g • toComplex τ := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]

  set a' : ℝ := (g : Matrix (Fin 2) (Fin 2) ℝ) 0 0
  set b' : ℝ := (g : Matrix (Fin 2) (Fin 2) ℝ) 0 1
  set c' : ℝ := (g : Matrix (Fin 2) (Fin 2) ℝ) 1 0
  set d' : ℝ := (g : Matrix (Fin 2) (Fin 2) ℝ) 1 1

  have hdet : a' * d' - b' * c' = 1 := by
    have hdet' := Matrix.SpecialLinearGroup.det_coe g
    rw [Matrix.det_fin_two] at hdet'
    exact hdet'

  apply Complex.ext
  · simpa [toComplex, moebius, a, b, c, d, denomSq, a', b', c', d'] using
      (real_moebius_re_algebra a' b' c' d' τ.x τ.y)
  · simpa [toComplex, moebius, c, d, denomSq, a', b', c', d'] using
      (real_moebius_im_algebra a' b' c' d' τ.x τ.y hdet)

private theorem mul_moebius (g h : SL2R) (τ : RealUpperHalfPlane) :
    moebius (g * h) τ = moebius g (moebius h τ) := by
  have H : toComplex (moebius (g * h) τ) = toComplex (moebius g (moebius h τ)) := by
    rw [toComplex_moebius, mul_smul, toComplex_moebius, toComplex_moebius]
  apply RealUpperHalfPlane.ext
  · exact (Complex.ext_iff.1 (UpperHalfPlane.ext_iff.1 H)).1
  · exact (Complex.ext_iff.1 (UpperHalfPlane.ext_iff.1 H)).2

instance : SMul SL2R RealUpperHalfPlane where
  smul := moebius

@[simp]
theorem smul_def (g : SL2R) (τ : RealUpperHalfPlane) :
    g • τ = moebius g τ := rfl

theorem one_smul_real (τ : RealUpperHalfPlane) : (1 : SL2R) • τ = τ := by
  simpa [SMul.smul, moebius] using one_moebius τ

theorem mul_smul_real (g h : SL2R) (τ : RealUpperHalfPlane) :
    (g * h : SL2R) • τ = g • (h • τ) := by
  simpa [SMul.smul] using mul_moebius g h τ

instance : MulAction SL2R RealUpperHalfPlane where
  one_smul := one_smul_real
  mul_smul := mul_smul_real

instance : MulAction SL2Z RealUpperHalfPlane :=
  MulAction.compHom _ (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ))

@[simp]
theorem sl2z_smul_def (g : SL2Z) (τ : RealUpperHalfPlane) :
    g • τ = ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) g) : SL2R) • τ := rfl

end RealUpperHalfPlane

end InfoGeometry.Geometry
