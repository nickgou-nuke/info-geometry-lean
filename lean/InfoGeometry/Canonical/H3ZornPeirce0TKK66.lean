/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
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


abbrev End10 := V10 →ₗ[ℝ] V10
abbrev End12 := V12 →ₗ[ℝ] V12

def InSO66 (T : End12) : Prop := ∀ x y : V12, B66 (T x) y + B66 x (T y) = 0

noncomputable def P (u : V10) : End12 where
  toFun x := ⟨-BQ10 u x.2.1, ⟨x.2.2 • u, 0⟩⟩
  map_add' x y := by ext <;> simp [BQ10_add_right, add_smul] <;> ring
  map_smul' r x := by ext <;> simp [BQ10_smul_right, smul_smul] <;> ring

noncomputable def K (v : V10) : End12 where
  toFun x := ⟨0, ⟨x.1 • v, -BQ10 v x.2.1⟩⟩
  map_add' x y := by ext <;> simp [BQ10_add_right, add_smul] <;> ring
  map_smul' r x := by ext <;> simp [BQ10_smul_right, smul_smul] <;> ring

noncomputable def D (lam : ℝ) : End12 where
  toFun x := ⟨lam * x.1, ⟨0, -lam * x.2.2⟩⟩
  map_add' x y := by ext <;> simp <;> ring
  map_smul' r x := by ext <;> simp <;> ring

noncomputable def Mrot (M : End10) : End12 where
  toFun x := ⟨0, ⟨M x.2.1, 0⟩⟩
  map_add' x y := by ext <;> simp
  map_smul' r x := by ext <;> simp

theorem Mrot_in_so66 (M : End10) (hM : InSO55BQ M) : InSO66 (Mrot M) := by
  intro x y
  simp only [InSO66, B66, Mrot, LinearMap.coe_mk, AddHom.coe_mk,
    zero_mul, mul_zero, zero_add, add_zero]
  exact hM x.2.1 y.2.1

def bracket (A B : End12) : End12 := A.comp B - B.comp A

def crossRotation (u v : V10) : End10 := (-1 / 2 : ℝ) • bivectorGen u v

theorem crossRotation_apply (u v z : V10) :
    crossRotation u v z = BQ10 u z • v - BQ10 v z • u := by
  ext i
  simp [crossRotation, bivectorGen]
  ring

theorem finrank_V12 : Module.finrank ℝ V12 = 12 := by
  simp [V12, finrank_minkowski10]

end InfoGeometry.Canonical.H3ZornPeirce0TKK66
