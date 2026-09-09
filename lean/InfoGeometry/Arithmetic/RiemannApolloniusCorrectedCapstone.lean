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
      norm_num [centered]
    · right
      norm_num [centered]

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
      exact (sub_eq_zero.mp hs1).symm
  · rintro (rfl | rfl) <;> simp [logarithmicScale]

/-- The two coordinate directions are orthogonal everywhere. -/
theorem apollonius_coordinate_orthogonality (sigma t : ℝ) :
    (rotationalField sigma t).1 * (dilationCoordinateField sigma t).1 +
      (rotationalField sigma t).2 * (dilationCoordinateField sigma t).2 = 0 :=
  rotational_dilation_orthogonal sigma t

end InfoGeometry.Arithmetic.RiemannApolloniusCorrectedCapstone

end noncomputable section
