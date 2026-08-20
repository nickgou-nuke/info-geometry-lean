import Mathlib

/-!
# Scalar logarithmic barrier

The scalar barrier `-log x` is treated on its positive domain.  The file proves
its first three derivatives, positivity of its Hessian, its exact
self-concordance equality, and the product-to-sum logarithmic law.
-/

noncomputable section

namespace InfoGeometry.Canonical.ScalarLogBarrier

/-- Scalar logarithmic barrier. -/
def barrier (x : ℝ) : ℝ :=
  -Real.log x

/-- First derivative of the barrier. -/
def gradient (x : ℝ) : ℝ :=
  -x⁻¹

/-- Second derivative of the barrier. -/
def hessian (x : ℝ) : ℝ :=
  (x ^ 2)⁻¹

/-- Third derivative of the barrier. -/
def thirdDerivative (x : ℝ) : ℝ :=
  -2 * (x ^ 3)⁻¹

/-- The logarithm converts products into sums on nonzero inputs. -/
theorem barrier_mul {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) :
    barrier (x * y) = barrier x + barrier y := by
  unfold barrier
  rw [Real.log_mul hx hy]
  ring

/-- First derivative of `-log`. -/
theorem hasDerivAt_barrier {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt barrier (gradient x) x := by
  unfold barrier gradient
  simpa using (Real.hasDerivAt_log hx).neg

/-- Derivative of the barrier gradient. -/
theorem hasDerivAt_gradient {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt gradient (hessian x) x := by
  unfold gradient hessian
  convert (hasDerivAt_inv hx).neg using 1
  ring

/-- Derivative of the barrier Hessian. -/
theorem hasDerivAt_hessian {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt hessian (thirdDerivative x) x := by
  unfold hessian thirdDerivative
  have hpow : x ^ 2 ≠ 0 := pow_ne_zero 2 hx
  have h := (hasDerivAt_pow 2 x).inv hpow
  convert h using 1
  field_simp [hx] <;> ring

@[simp] theorem deriv_barrier {x : ℝ} (hx : x ≠ 0) :
    deriv barrier x = gradient x :=
  (hasDerivAt_barrier hx).deriv

@[simp] theorem deriv_gradient {x : ℝ} (hx : x ≠ 0) :
    deriv gradient x = hessian x :=
  (hasDerivAt_gradient hx).deriv

@[simp] theorem deriv_hessian {x : ℝ} (hx : x ≠ 0) :
    deriv hessian x = thirdDerivative x :=
  (hasDerivAt_hessian hx).deriv

/-- The scalar log barrier is strictly convex on the positive ray. -/
theorem hessian_pos {x : ℝ} (hx : 0 < x) :
    0 < hessian x := by
  unfold hessian
  exact inv_pos.mpr (pow_pos hx 2)

/-- Exact square form of the self-concordance equality. -/
theorem thirdDerivative_sq_eq_four_mul_hessian_cube
    {x : ℝ} (hx : x ≠ 0) :
    (thirdDerivative x) ^ 2 = 4 * (hessian x) ^ 3 := by
  unfold thirdDerivative hessian
  field_simp [hx] <;> ring

/-- Directional scalar self-concordance equality. -/
theorem directional_selfConcordance_sq
    {x h : ℝ} (hx : x ≠ 0) :
    (thirdDerivative x * h ^ 3) ^ 2 =
      4 * (hessian x * h ^ 2) ^ 3 := by
  calc
    (thirdDerivative x * h ^ 3) ^ 2 =
        (thirdDerivative x) ^ 2 * h ^ 6 := by ring
    _ = (4 * (hessian x) ^ 3) * h ^ 6 := by
          rw [thirdDerivative_sq_eq_four_mul_hessian_cube hx]
    _ = 4 * (hessian x * h ^ 2) ^ 3 := by ring

/-- Reciprocal scaling reverses the scalar barrier sign. -/
theorem barrier_inv (x : ℝ) :
    barrier x⁻¹ = -barrier x := by
  unfold barrier
  rw [Real.log_inv]
  ring

end InfoGeometry.Canonical.ScalarLogBarrier

end noncomputable section
