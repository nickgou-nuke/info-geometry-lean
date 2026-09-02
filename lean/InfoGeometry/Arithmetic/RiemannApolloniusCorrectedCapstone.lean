import Mathlib.Tactic
import InfoGeometry.Arithmetic.RiemannApolloniusRiccatiBridge
import InfoGeometry.Arithmetic.RiemannApolloniusVectorFields
/-!
# Corrected Apollonius coordinate capstone

This file packages the exact finite consequences of the ratio coordinate
`w(s)=s/(s-1)` and explicitly separates two notions that must not be conflated:

* the affine fixed point of the reflection `s ↦ 1-s`, namely `s=1/2`;
* the two zeros of the Riccati scale `s(1-s)`, namely `s=0,1`.

It also records the orthogonal phase/dilation coordinate split induced by
`log w = -u + i theta`.  No RH, Hilbert--Polya, attractor, or essential
self-adjointness theorem is inferred.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.RiemannApolloniusCorrectedCapstone

open Complex
open InfoGeometry.Arithmetic.RiemannApolloniusRiccatiBridge
open InfoGeometry.Arithmetic.RiemannApolloniusVectorFields

/-- The reflection midpoint is centered at zero. -/
@[simp] theorem centered_reflection_midpoint :
    centered (1 / 2 : ℂ) = 0 := by
  simp [centered]

/-- The reflection midpoint is not a zero of the Riccati scale. -/
theorem reflection_midpoint_not_riccati_fixed :
    centeredScale 0 ≠ 0 := by
  norm_num [centeredScale]

/-- The two Riccati fixed points in the original `s` coordinate are exactly
`0` and `1`. -/
theorem riccati_fixed_points_uncentered (s : ℂ) :
    centeredScale (centered s) = 0 ↔ s = 1 ∨ s = 0 := by
  rw [centeredScale_eq_zero_iff]
  constructor
  · rintro (h | h)
    · left
      unfold centered at h
      linear_combination h
    · right
      unfold centered at h
      linear_combination h
  · rintro (rfl | rfl)
    · left
      simp [centered]
    · right
      simp [centered]

/-- Equivalently, the original logarithmic scale vanishes exactly at `0` or
`1`. -/
theorem logarithmicScale_eq_zero_iff (s : ℂ) :
    logarithmicScale s = 0 ↔ s = 0 ∨ s = 1 := by
  unfold logarithmicScale
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hs0 | hs1
    · exact Or.inl hs0
    · right
      linear_combination hs1
  · rintro (rfl | rfl) <;> simp [logarithmicScale]

/-- The phase field is tangent to the critical line while the `u` coordinate
field is normal to it. -/
theorem critical_line_tangent_normal_packet (t : ℝ) :
    (rotationalField (1 / 2) t).1 = 0 ∧
    (dilationCoordinateField (1 / 2) t).2 = 0 ∧
    (rotationalField (1 / 2) t).2 = 1 / 4 + t ^ 2 ∧
    (dilationCoordinateField (1 / 2) t).1 = -(1 / 4 + t ^ 2) :=
  ⟨rotationalField_criticalLine_transverse_zero t,
    dilationCoordinateField_criticalLine_longitudinal_zero t,
    rotationalField_criticalLine_longitudinal t,
    dilationCoordinateField_criticalLine_transverse t⟩

/-- The two coordinate directions are orthogonal everywhere. -/
theorem apollonius_coordinate_orthogonality (sigma t : ℝ) :
    (rotationalField sigma t).1 * (dilationCoordinateField sigma t).1 +
      (rotationalField sigma t).2 * (dilationCoordinateField sigma t).2 = 0 :=
  rotational_dilation_orthogonal sigma t

/-- Compact corrected packet. -/
theorem corrected_apollonius_packet (s : ℂ) (sigma t : ℝ) :
    (1 - s = s ↔ s = (1 / 2 : ℂ)) ∧
    (logarithmicScale s = 0 ↔ s = 0 ∨ s = 1) ∧
    ((rotationalField sigma t).1 * (dilationCoordinateField sigma t).1 +
      (rotationalField sigma t).2 * (dilationCoordinateField sigma t).2 = 0) :=
  ⟨reflection_fixed_iff s,
    logarithmicScale_eq_zero_iff s,
    apollonius_coordinate_orthogonality sigma t⟩

end InfoGeometry.Arithmetic.RiemannApolloniusCorrectedCapstone

end noncomputable section
