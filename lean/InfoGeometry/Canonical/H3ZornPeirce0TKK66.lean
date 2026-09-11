import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.H3ZornPeirce0SO55

/-! The native null extension boundary for the Peirce-0 quadratic carrier.

The carrier and bilinear form are formalized here.  The conformal generator
maps are kept as ordinary functions until their linearity and skewness
hypotheses are supplied in a dedicated owner.
-/
noncomputable section
namespace InfoGeometry.Canonical.H3ZornPeirce0TKK66

open InfoGeometry.Algebra
open InfoGeometry.Canonical.H3ZornPeirce0QuadraticRepresentation
open InfoGeometry.Canonical.H3ZornPeirce0QuadraticHomothety
open InfoGeometry.Canonical.H3ZornPeirce0SO55

abbrev V10 := Minkowski10
abbrev V12 := ℝ × V10 × ℝ

def B66 (x y : V12) : ℝ :=
  x.1 * y.2.2 + x.2.2 * y.1 + BQ10 x.2.1 y.2.1

@[simp] theorem B66_comm (x y : V12) : B66 x y = B66 y x := by
  rw [B66, B66, BQ10_comm]
  ring

def translation (u : V10) (x : V12) : V12 :=
  ⟨-BQ10 u x.2.1, ⟨x.2.2 • u, 0⟩⟩

def specialConformal (v : V10) (x : V12) : V12 :=
  ⟨0, ⟨x.1 • v, -BQ10 v x.2.1⟩⟩

def dilation (scale : ℝ) (x : V12) : V12 :=
  ⟨scale * x.1, ⟨0, -scale * x.2.2⟩⟩

def middleAction (M : V10 → V10) (x : V12) : V12 :=
  ⟨0, ⟨M x.2.1, 0⟩⟩

theorem translation_is_skew (u : V10) (x y : V12) :
    B66 (translation u x) y + B66 x (translation u y) = 0 := by
  rw [B66, B66, translation, translation]
  rw [BQ10_smul_left, BQ10_smul_right, BQ10_comm x.2.1 u]
  ring

theorem specialConformal_is_skew (v : V10) (x y : V12) :
    B66 (specialConformal v x) y + B66 x (specialConformal v y) = 0 := by
  rw [B66, B66, specialConformal, specialConformal]
  rw [BQ10_smul_left, BQ10_smul_right, BQ10_comm x.2.1 v]
  ring

theorem dilation_is_skew (scale : ℝ) (x y : V12) :
    B66 (dilation scale x) y + B66 x (dilation scale y) = 0 := by
  have hz (u : V10) : BQ10 u 0 = 0 := by
    simpa using BQ10_smul_right (0 : ℝ) u (0 : V10)
  have hzL (u : V10) : BQ10 0 u = 0 := by
    rw [BQ10_comm]
    exact hz u
  rw [B66, B66, dilation]
  simp [dilation, hz, hzL]
  ring

theorem so66_dimension_numeral : 12 * (12 - 1) / 2 = 66 := by
  norm_num

end InfoGeometry.Canonical.H3ZornPeirce0TKK66
