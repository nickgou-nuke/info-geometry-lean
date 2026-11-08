import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

import InfoGeometry.Canonical.ProjectiveAffineConformalClosure55
import InfoGeometry.Canonical.PauliHestenesSpinMomentum
import InfoGeometry.Projective.KleinQuadric

/-! A finite algebraic bridge from the existing split `(4,4)` carrier to a
real `(2,4)` slice and its complex Klein-cone readback.  This file does not
assert a topological compactification or a twistor incidence theorem. -/

noncomputable section

namespace InfoGeometry.Bridge.ZornConformalSixCone

open ProjectiveAffineConformalClosure55
open InfoGeometry.Canonical.PauliHestenesSpinMomentum
open InfoGeometry.Projective.KleinQuadric

structure ConformalSix where
  a0 : ℝ
  ax : ℝ
  ay : ℝ
  az : ℝ
  b0 : ℝ
  bz : ℝ

def quadratic24 (X : ConformalSix) : ℝ :=
  X.a0 ^ 2 + X.bz ^ 2 - (X.ax ^ 2 + X.ay ^ 2 + X.az ^ 2 + X.b0 ^ 2)

def toPACSplit44 (X : ConformalSix) : PACSplit44 where
  x0 := X.a0
  x1 := 0
  x2 := 0
  x3 := X.bz
  y0 := X.b0
  y1 := X.ax
  y2 := X.ay
  y3 := X.az

@[simp] theorem Q44_toPACSplit44 (X : ConformalSix) :
    Q44 (toPACSplit44 X) = quadratic24 X := by
  simp [Q44, toPACSplit44, quadratic24]
  ring

def scale (c : ℝ) (X : ConformalSix) : ConformalSix where
  a0 := c * X.a0; ax := c * X.ax; ay := c * X.ay
  az := c * X.az; b0 := c * X.b0; bz := c * X.bz

theorem quadratic24_scale (c : ℝ) (X : ConformalSix) :
    quadratic24 (scale c X) = c ^ 2 * quadratic24 X := by
  cases X
  simp [quadratic24, scale]
  ring

def diracConeEmbedding (κ : ℝ) (P : PauliParavector) : ConformalSix where
  a0 := κ * P.energy
  ax := κ * P.px
  ay := κ * P.py
  az := κ * P.pz
  b0 := κ * (1 + P.minkowskiNormSq) / 2
  bz := κ * (1 - P.minkowskiNormSq) / 2

@[simp] theorem diracConeEmbedding_affine_gauge (κ : ℝ) (P : PauliParavector) :
    (diracConeEmbedding κ P).b0 + (diracConeEmbedding κ P).bz = κ := by
  simp [diracConeEmbedding]
  ring

@[simp] theorem diracConeEmbedding_complementary_gauge (κ : ℝ) (P : PauliParavector) :
    (diracConeEmbedding κ P).b0 - (diracConeEmbedding κ P).bz =
      κ * P.minkowskiNormSq := by
  simp [diracConeEmbedding]
  ring

theorem diracConeEmbedding_null (κ : ℝ) (P : PauliParavector) :
    quadratic24 (diracConeEmbedding κ P) = 0 := by
  simp [quadratic24, diracConeEmbedding,
    PauliParavector.minkowskiNormSq]
  ring

theorem diracConeEmbedding_PACSplit44_null (κ : ℝ) (P : PauliParavector) :
    Q44 (toPACSplit44 (diracConeEmbedding κ P)) = 0 := by
  rw [Q44_toPACSplit44, diracConeEmbedding_null]

theorem diracConeEmbedding_scale (c κ : ℝ) (P : PauliParavector) :
    diracConeEmbedding (c * κ) P = scale c (diracConeEmbedding κ P) := by
  cases P
  dsimp [diracConeEmbedding, scale]
  congr 1 <;> ring

def affineReadback (X : ConformalSix) : PauliParavector where
  energy := X.a0; px := X.ax; py := X.ay; pz := X.az

@[simp] theorem affineReadback_diracConeEmbedding_one (P : PauliParavector) :
    affineReadback (diracConeEmbedding 1 P) = P := by
  cases P
  simp [affineReadback, diracConeEmbedding]

theorem diracConeEmbedding_one_injective :
    Function.Injective (diracConeEmbedding 1) :=
  Function.LeftInverse.injective affineReadback_diracConeEmbedding_one

def toComplexPlucker (X : ConformalSix) : Plucker6 ℂ where
  p01 := ((X.a0 + X.b0 : ℝ) : ℂ)
  p02 := (X.ax : ℂ) + Complex.I * (X.ay : ℂ)
  p03 := ((X.bz + X.az : ℝ) : ℂ)
  p12 := ((X.bz - X.az : ℝ) : ℂ)
  p13 := (X.ax : ℂ) - Complex.I * (X.ay : ℂ)
  p23 := ((X.a0 - X.b0 : ℝ) : ℂ)

theorem kleinQ_toComplexPlucker (X : ConformalSix) :
    Plucker6.kleinQ (toComplexPlucker X) = (quadratic24 X : ℂ) := by
  simp [Plucker6.kleinQ, toComplexPlucker, quadratic24]
  ring_nf
  rw [Complex.I_sq]
  ring

theorem diracConeEmbedding_isKlein (κ : ℝ) (P : PauliParavector) :
    Plucker6.IsKlein (toComplexPlucker (diracConeEmbedding κ P)) := by
  unfold Plucker6.IsKlein
  rw [kleinQ_toComplexPlucker, diracConeEmbedding_null]
  exact_mod_cast (rfl : (0 : ℝ) = 0)

theorem zorn_conformal_six_cone_packet (κ : ℝ) (P : PauliParavector) :
    (toPACSplit44 (diracConeEmbedding κ P)).x1 = 0 ∧
    (toPACSplit44 (diracConeEmbedding κ P)).x2 = 0 ∧
    Q44 (toPACSplit44 (diracConeEmbedding κ P)) = 0 ∧
    Plucker6.IsKlein (toComplexPlucker (diracConeEmbedding κ P)) := by
  exact ⟨rfl, rfl, diracConeEmbedding_PACSplit44_null κ P,
    diracConeEmbedding_isKlein κ P⟩

end InfoGeometry.Bridge.ZornConformalSixCone

end noncomputable section
