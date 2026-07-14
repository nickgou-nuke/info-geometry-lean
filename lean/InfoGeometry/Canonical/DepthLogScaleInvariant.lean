import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# InfoGeometry.Canonical.DepthLogScaleInvariant

Finite log-scale invariants for binary/fractal operator towers.

This file proves the scalar algebraic kernel behind the tensor-tower
normalization:

* raw determinant scale changes by squaring;
* logarithms turn squaring into doubling;
* dividing by the doubled depth/volume makes the quantity invariant;
* inversion reverses log-scale time.

No operator limit.
No loop-group claim.
No compactification theorem.
No wrappers.
No `sorry`.
-/

namespace DepthLogScaleInvariant

noncomputable section

/--
Depth-normalized logarithmic scale.

Think of `d` as the current finite volume/depth normalization.
-/
def normalizedLog (d x : ℝ) : ℝ :=
  (1 / d) * Real.log x

/--
Logarithm of a square.

For positive `x`,

  log(x²) = 2 log(x).
-/
theorem log_square_of_pos
    {x : ℝ} (hx : 0 < x) :
    Real.log (x ^ 2) = (2 : ℝ) * Real.log x := by
  have hxne : x ≠ 0 := ne_of_gt hx
  rw [show x ^ 2 = x * x by ring]
  rw [Real.log_mul hxne hxne]
  ring

/--
One binary depth step preserves the normalized logarithmic scale.

Raw scale:

  x ↦ x².

Depth/volume normalization:

  d ↦ 2d.

Invariant:

  (1/(2d)) log(x²) = (1/d) log(x).
-/
theorem normalizedLog_square_depthStep
    {d x : ℝ}
    (hd : d ≠ 0)
    (hx : 0 < x) :
    normalizedLog ((2 : ℝ) * d) (x ^ 2)
      =
    normalizedLog d x := by
  unfold normalizedLog
  rw [log_square_of_pos hx]
  have h2d : (2 : ℝ) * d ≠ 0 := by
    exact mul_ne_zero (by norm_num) hd
  field_simp [hd, h2d]

/--
Named binary tensor-tower determinant step.

If the determinant at the next stage is the square of the previous determinant,
then the normalized log determinant is unchanged.
-/
theorem normalizedLog_detTensorStep
    {d detOld detNew : ℝ}
    (hd : d ≠ 0)
    (hdetOld : 0 < detOld)
    (hdetNew : detNew = detOld ^ 2) :
    normalizedLog ((2 : ℝ) * d) detNew
      =
    normalizedLog d detOld := by
  rw [hdetNew]
  exact normalizedLog_square_depthStep hd hdetOld

/--
Logarithm converts multiplication of nonzero positive scales into addition.

This is the additive cocycle form of a multiplicative scale character.
-/
theorem normalizedLog_mul_of_nonzero
    {d x y : ℝ}
    (hx : x ≠ 0)
    (hy : y ≠ 0) :
    normalizedLog d (x * y)
      =
    normalizedLog d x + normalizedLog d y := by
  unfold normalizedLog
  rw [Real.log_mul hx hy]
  ring

/--
Log-scale inversion.

For positive `x`,

  log(x⁻¹) = -log(x).

This is the finite algebraic form of time reversal in log-scale coordinates.
-/
theorem log_inv_of_pos
    {x : ℝ} (hx : 0 < x) :
    Real.log x⁻¹ = - Real.log x := by
  have hxne : x ≠ 0 := ne_of_gt hx
  have hxin : x⁻¹ ≠ 0 := inv_ne_zero hxne
  have hlog :
      Real.log (x⁻¹ * x) =
        Real.log x⁻¹ + Real.log x :=
    Real.log_mul hxin hxne
  have hxprod : x⁻¹ * x = 1 := by
    field_simp [hxne]
  rw [hxprod, Real.log_one] at hlog
  linarith

/--
Normalized log-scale inversion.

Inversion reverses the sign of normalized log time.
-/
theorem normalizedLog_inv_of_pos
    {d x : ℝ}
    (hx : 0 < x) :
    normalizedLog d x⁻¹ = - normalizedLog d x := by
  unfold normalizedLog
  rw [log_inv_of_pos hx]
  ring

/--
A scale and its inverse cancel in normalized log coordinates.
-/
theorem normalizedLog_inv_cancel
    {d x : ℝ}
    (hx : 0 < x) :
    normalizedLog d x + normalizedLog d x⁻¹ = 0 := by
  rw [normalizedLog_inv_of_pos (d := d) hx]
  ring

/--
Binary depth increment has zero normalized logarithmic defect.

This isolates the immutable piece:

  normalizedLog(2d, x²) - normalizedLog(d, x) = 0.
-/
theorem normalizedLog_binary_defect_zero
    {d x : ℝ}
    (hd : d ≠ 0)
    (hx : 0 < x) :
    normalizedLog ((2 : ℝ) * d) (x ^ 2)
      - normalizedLog d x = 0 := by
  rw [normalizedLog_square_depthStep hd hx]
  ring

end

end DepthLogScaleInvariant
