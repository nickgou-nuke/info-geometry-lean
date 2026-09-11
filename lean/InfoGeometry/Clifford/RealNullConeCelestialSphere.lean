import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Future null directions and the celestial sphere

The finite real core of the celestial-sphere construction: a future null
vector in Minkowski signature `(+, -, -, -)` normalizes by its positive time
coordinate to a unit spatial direction.  Projective and conformal quotient
identifications are deliberately left to downstream owners.
-/

noncomputable section

namespace InfoGeometry.Clifford.RealNullConeCelestialSphere

structure MinkowskiVector where
  time : ℝ
  x : ℝ
  y : ℝ
  z : ℝ

def minkowskiQuadratic (v : MinkowskiVector) : ℝ :=
  v.time ^ 2 - v.x ^ 2 - v.y ^ 2 - v.z ^ 2

def futureNull (v : MinkowskiVector) : Prop :=
  0 < v.time ∧ minkowskiQuadratic v = 0

def spatialDirection (v : MinkowskiVector) : ℝ × ℝ × ℝ :=
  (v.x / v.time, v.y / v.time, v.z / v.time)

def unitSpatialDirection (d : ℝ × ℝ × ℝ) : Prop :=
  d.1 ^ 2 + d.2.1 ^ 2 + d.2.2 ^ 2 = 1

theorem futureNull_time_ne_zero {v : MinkowskiVector} (hv : futureNull v) :
    v.time ≠ 0 := by
  exact ne_of_gt hv.1

theorem futureNull_direction_on_sphere {v : MinkowskiVector}
    (hv : futureNull v) : unitSpatialDirection (spatialDirection v) := by
  rcases hv with ⟨ht, hnull⟩
  unfold minkowskiQuadratic at hnull
  unfold unitSpatialDirection spatialDirection
  have htime : v.time ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt ht)
  field_simp [htime]
  nlinarith [hnull]

def positiveScale (a : ℝ) (v : MinkowskiVector) : MinkowskiVector :=
  { time := a * v.time
    x := a * v.x
    y := a * v.y
    z := a * v.z }

theorem minkowskiQuadratic_positiveScale (a : ℝ) (v : MinkowskiVector) :
    minkowskiQuadratic (positiveScale a v) = a ^ 2 * minkowskiQuadratic v := by
  unfold minkowskiQuadratic positiveScale
  ring

theorem futureNull_positiveScale {a : ℝ} (ha : 0 < a)
    {v : MinkowskiVector} (hv : futureNull v) :
    futureNull (positiveScale a v) := by
  refine ⟨mul_pos ha hv.1, ?_⟩
  rw [minkowskiQuadratic_positiveScale, hv.2, mul_zero]

theorem spatialDirection_positiveScale {a : ℝ} (ha : 0 < a)
    (v : MinkowskiVector) :
    spatialDirection (positiveScale a v) = spatialDirection v := by
  unfold spatialDirection positiveScale
  have hav : a ≠ 0 := ne_of_gt ha
  simp only [div_eq_mul_inv]
  ext <;> field_simp [hav]

theorem futureNull_is_unit_direction {v : MinkowskiVector}
    (hv : futureNull v) :
    (spatialDirection v).1 ^ 2 +
      (spatialDirection v).2.1 ^ 2 +
      (spatialDirection v).2.2 ^ 2 = 1 :=
  futureNull_direction_on_sphere hv

end InfoGeometry.Clifford.RealNullConeCelestialSphere

end noncomputable section
