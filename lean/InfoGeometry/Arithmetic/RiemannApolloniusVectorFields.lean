import Mathlib.Tactic
import InfoGeometry.Arithmetic.RiemannApolloniusRiccatiBridge

/-!
# Corrected Apollonius rotational/dilation vector fields

For the ratio coordinate

  w(s) = s / (s - 1) = exp (-u + i theta)

and the corrected logarithmic scale

  h(s) = ds / d log(w) = s (1 - s),

this file records the exact real two-component fields induced by the theta and
u coordinate directions.  The orientation is fixed by `log w = -u + i theta`:

  d s / d theta = i h(s),
  d s / d u     = - h(s).

The two fields are pointwise orthogonal in the Euclidean plane.  No global ODE
attractor statement is asserted: such a theorem requires a chosen dissipative
sign/potential and analytic flow hypotheses beyond these coordinate identities.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.RiemannApolloniusVectorFields

open Complex
open InfoGeometry.Arithmetic.RiemannApolloniusRiccatiBridge

/-- Real part of `s(1-s)` at `s = sigma + i t`. -/
def scaleA (sigma t : ℝ) : ℝ :=
  sigma * (1 - sigma) + t ^ 2

/-- Imaginary part of `s(1-s)` at `s = sigma + i t`. -/
def scaleB (sigma t : ℝ) : ℝ :=
  (1 - 2 * sigma) * t

/-- Complex reconstruction of the corrected logarithmic scale. -/
theorem logarithmicScale_real_coordinates (sigma t : ℝ) :
    logarithmicScale ((sigma : ℂ) + Complex.I * (t : ℂ)) =
      (scaleA sigma t : ℂ) + Complex.I * (scaleB sigma t : ℂ) := by
  unfold logarithmicScale scaleA scaleB
  apply Complex.ext <;> simp [mul_re, mul_im, sub_re, sub_im]
  · have hpow : ((t : ℂ) ^ 2).re = t ^ 2 := by
      norm_num [pow_two, Complex.mul_re]
    rw [hpow]
    ring
  · have hpow : ((t : ℂ) ^ 2).im = 0 := by
      norm_num [pow_two, Complex.mul_im]
    rw [hpow]
    ring

/-- Centered form of the real scale component. -/
theorem scaleA_centered (sigma t : ℝ) :
    scaleA sigma t =
      1 / 4 - (sigma - 1 / 2) ^ 2 + t ^ 2 := by
  unfold scaleA
  ring

/-- Centered form of the imaginary scale component. -/
theorem scaleB_centered (sigma t : ℝ) :
    scaleB sigma t = -2 * (sigma - 1 / 2) * t := by
  unfold scaleB
  ring

/-- The phase/rotational field induced by `d/d theta`: `ds/dtheta = i h`. -/
def rotationalField (sigma t : ℝ) : ℝ × ℝ :=
  (- scaleB sigma t, scaleA sigma t)

/-- The `u`-coordinate field induced by `d/du`: `ds/du = -h`. -/
def dilationCoordinateField (sigma t : ℝ) : ℝ × ℝ :=
  (- scaleA sigma t, - scaleB sigma t)

/-- Complex form of the phase field. -/
theorem rotationalField_complex (sigma t : ℝ) :
    ((rotationalField sigma t).1 : ℂ) +
        Complex.I * ((rotationalField sigma t).2 : ℂ) =
      Complex.I * logarithmicScale ((sigma : ℂ) + Complex.I * (t : ℂ)) := by
  rw [logarithmicScale_real_coordinates]
  unfold rotationalField
  simp
  apply Complex.ext <;> simp
  <;> ring

/-- Complex form of the `u`-coordinate field. -/
theorem dilationCoordinateField_complex (sigma t : ℝ) :
    ((dilationCoordinateField sigma t).1 : ℂ) +
        Complex.I * ((dilationCoordinateField sigma t).2 : ℂ) =
      - logarithmicScale ((sigma : ℂ) + Complex.I * (t : ℂ)) := by
  rw [logarithmicScale_real_coordinates]
  unfold dilationCoordinateField
  simp
  apply Complex.ext <;> simp

/-- The two coordinate fields are pointwise Euclidean-orthogonal. -/
theorem rotational_dilation_orthogonal (sigma t : ℝ) :
    (rotationalField sigma t).1 * (dilationCoordinateField sigma t).1 +
      (rotationalField sigma t).2 * (dilationCoordinateField sigma t).2 = 0 := by
  unfold rotationalField dilationCoordinateField
  ring

/-- The rotational field is tangent to the critical line: its transverse
component vanishes at `sigma = 1/2`. -/
theorem rotationalField_criticalLine_transverse_zero (t : ℝ) :
    (rotationalField (1 / 2) t).1 = 0 := by
  simp [rotationalField, scaleB]

/-- On the critical line the longitudinal rotational speed is `1/4 + t^2`. -/
theorem rotationalField_criticalLine_longitudinal (t : ℝ) :
    (rotationalField (1 / 2) t).2 = 1 / 4 + t ^ 2 := by
  simp [rotationalField, scaleA]
  ring

/-- The `u` coordinate direction is purely transverse on the critical line. -/
theorem dilationCoordinateField_criticalLine_longitudinal_zero (t : ℝ) :
    (dilationCoordinateField (1 / 2) t).2 = 0 := by
  simp [dilationCoordinateField, scaleB]

/-- The transverse `u` coordinate speed on the critical line.  Its sign follows
from the convention `log w = -u + i theta`; it is not itself an attractor law. -/
theorem dilationCoordinateField_criticalLine_transverse (t : ℝ) :
    (dilationCoordinateField (1 / 2) t).1 = -(1 / 4 + t ^ 2) := by
  simp [dilationCoordinateField, scaleA]
  ring

/-- The rotational vector field is the real form of the Riccati polynomial
`i (1/4-z^2)` after centering. -/
theorem rotationalField_centered_complex (delta t : ℝ) :
    let z : ℂ := (delta : ℂ) + Complex.I * (t : ℂ)
    (((rotationalField (delta + 1 / 2) t).1 : ℂ) +
      Complex.I * ((rotationalField (delta + 1 / 2) t).2 : ℂ)) =
      Complex.I * centeredScale z := by
  intro z
  rw [rotationalField_complex]
  rw [logarithmicScale_centered]
  congr 1
  apply Complex.ext <;>
    simp [centeredScale, centered, z, Complex.mul_re, Complex.mul_im] <;>
    ring

/-- Master finite coordinate packet. -/
theorem apollonius_vector_field_packet (sigma t : ℝ) :
    ((rotationalField sigma t).1 * (dilationCoordinateField sigma t).1 +
      (rotationalField sigma t).2 * (dilationCoordinateField sigma t).2 = 0) ∧
    (scaleA sigma t = 1 / 4 - (sigma - 1 / 2) ^ 2 + t ^ 2) ∧
    (scaleB sigma t = -2 * (sigma - 1 / 2) * t) :=
  ⟨rotational_dilation_orthogonal sigma t,
    scaleA_centered sigma t,
    scaleB_centered sigma t⟩

end InfoGeometry.Arithmetic.RiemannApolloniusVectorFields

end noncomputable section
