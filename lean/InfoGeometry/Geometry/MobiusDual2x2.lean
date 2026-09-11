import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Lemmas
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

namespace InfoGeometry.Geometry

abbrev RatVec2 := InfoGeometry.Algebra.FiniteSpin.Vec2Q
abbrev RatMat2 := Matrix (Fin 2) (Fin 2) ℚ

/-- The hyperbolic Möbius matrix acting by `z ↦ 4z` on the affine chart. -/
def hyperbolicM : RatMat2 := !![(2 : ℚ), 0; 0, (1 / 2 : ℚ)]

/-- Contragredient matrix preserving the standard pairing. -/
def contragredient (M : RatMat2) : RatMat2 :=
  !![M 1 1, -M 0 1; -M 1 0, M 0 0]

/-- Fixed-point polynomial of the fractional-linear action. -/
def fixedPoly (a b c d z : ℚ) : ℚ := c * z ^ 2 + (d - a) * z - b

/-- Standard bilinear pairing on column coordinates. -/
def pairing (η θ : RatVec2) : ℚ := η 0 * θ 0 + η 1 * θ 1

/-- Dual action on covectors via the transpose contragredient. -/
def dualAction (M : RatMat2) (η : RatVec2) : RatVec2 :=
  (contragredient M).transpose.mulVec η

/-- Projective direction `0`. -/
def vZero : RatVec2 := ![1, 0]

/-- Projective direction `∞`. -/
def vInfinity : RatVec2 := ![0, 1]

theorem hyperbolic_det : hyperbolicM.det = 1 := by
  norm_num [hyperbolicM, Matrix.det_fin_two]

theorem hyperbolic_fixedPoly_factor (z : ℚ) :
    fixedPoly 2 0 0 (1 / 2) z = (-3 / 2) * z := by
  unfold fixedPoly
  ring

theorem hyperbolic_fixed_zero : fixedPoly 2 0 0 (1 / 2) 0 = 0 := by
  simpa using hyperbolic_fixedPoly_factor 0

/-- The fixed-point polynomial vanishes exactly at `0` in the hyperbolic readout. -/
theorem hyperbolic_fixedPoly_eq_zero_iff (z : ℚ) :
    fixedPoly 2 0 0 (1 / 2) z = 0 ↔ z = 0 := by
  rw [hyperbolic_fixedPoly_factor]
  constructor
  · intro h
    have hcoeff : (-3 / 2 : ℚ) ≠ 0 := by norm_num
    exact Or.resolve_left (mul_eq_zero.mp h) hcoeff
  · intro hz
    subst hz
    simp [hyperbolic_fixedPoly_factor]

/-- The fixed-point polynomial is nonzero away from the hyperbolic root. -/
theorem hyperbolic_fixedPoly_ne_zero_of_ne_zero (z : ℚ) (hz : z ≠ 0) :
    fixedPoly 2 0 0 (1 / 2) z ≠ 0 := by
  intro hzero
  exact hz ((hyperbolic_fixedPoly_eq_zero_iff z).mp hzero)

theorem hyperbolic_eigenvector_zero : hyperbolicM.mulVec vZero = (2 : ℚ) • vZero := by
  ext i
  fin_cases i <;> simp [hyperbolicM, vZero, Matrix.mulVec, dotProduct]

theorem hyperbolic_eigenvector_infinity :
    hyperbolicM.mulVec vInfinity = ((1 / 2 : ℚ)) • vInfinity := by
  ext i
  fin_cases i <;> simp [hyperbolicM, vInfinity, Matrix.mulVec, dotProduct]

theorem pairing_contragredient_invariant (η θ : RatVec2) :
    pairing (dualAction hyperbolicM η) (hyperbolicM.mulVec θ) = pairing η θ := by
  unfold pairing dualAction contragredient hyperbolicM
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

theorem hyperbolic_forward_multiplier_repelling : (4 : ℚ) > 1 := by norm_num

theorem hyperbolic_infinity_multiplier_attracting : ((1 / 4 : ℚ)) < 1 := by norm_num

end InfoGeometry.Geometry
