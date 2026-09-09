import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-!
# Positive focal pairs, rapidity, and the hyperbolic-secant overlap

For positive `u` and `v`, the rapidity convention is `log (v / u) / 2`.
The geometric mean is constructed exponentially, then identified with
`Real.sqrt (u * v)`. This gives the exact null-coordinate reconstruction,
the difference/sum formula for `tanh`, and the geometric-mean/arithmetic-mean
formula for the reciprocal of `cosh`.

The Lorentz quadratic identity below concerns an auxiliary two-dimensional
carrier. It does not change the signature of a Euclidean detector metric.
No propagation equation or physical soliton claim is assumed here.
-/

noncomputable section

namespace InfoGeometry.Nuclear.FocalRapidity

/-- Half of the logarithmic ratio, with `v` in the numerator. -/
def rapidity (u v : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.log (v / u)

/-- Positive scale; on the positive quadrant it is the geometric mean. -/
def scale (u v : ℝ) : ℝ :=
  Real.exp ((Real.log u + Real.log v) / 2)

/-- The hyperbolic-secant profile, expressed with native Mathlib `Real.cosh`. -/
def sechProfile (x : ℝ) : ℝ :=
  1 / Real.cosh x

/-- Symmetric, dimensionless overlap of a positive focal pair. -/
def overlap (u v : ℝ) : ℝ :=
  2 * Real.sqrt (u * v) / (u + v)

variable {u v : ℝ}

theorem rapidity_eq_log_sub (hu : 0 < u) (hv : 0 < v) :
    rapidity u v = (Real.log v - Real.log u) / 2 := by
  rw [rapidity, Real.log_div (ne_of_gt hv) (ne_of_gt hu)]
  ring

theorem exp_two_rapidity (hu : 0 < u) (hv : 0 < v) :
    Real.exp (2 * rapidity u v) = v / u := by
  have h : 2 * rapidity u v = Real.log (v / u) := by
    dsimp [rapidity]
    ring
  rw [h, Real.exp_log (div_pos hv hu)]

theorem scale_pos (u v : ℝ) : 0 < scale u v :=
  Real.exp_pos _

theorem scale_sq (hu : 0 < u) (hv : 0 < v) :
    scale u v ^ 2 = u * v := by
  dsimp [scale]
  rw [pow_two, ← Real.exp_add]
  have h : (Real.log u + Real.log v) / 2 +
      (Real.log u + Real.log v) / 2 = Real.log u + Real.log v := by ring
  rw [h, Real.exp_add, Real.exp_log hu, Real.exp_log hv]

theorem sqrt_product_eq_scale (hu : 0 < u) (hv : 0 < v) :
    Real.sqrt (u * v) = scale u v := by
  rw [← scale_sq hu hv, Real.sqrt_sq (le_of_lt (scale_pos u v))]

theorem scale_mul_exp_rapidity (hu : 0 < u) (hv : 0 < v) :
    scale u v * Real.exp (rapidity u v) = v := by
  rw [scale, rapidity_eq_log_sub hu hv, ← Real.exp_add]
  have h : (Real.log u + Real.log v) / 2 +
      (Real.log v - Real.log u) / 2 = Real.log v := by ring
  rw [h, Real.exp_log hv]

theorem scale_mul_exp_neg_rapidity (hu : 0 < u) (hv : 0 < v) :
    scale u v * Real.exp (-rapidity u v) = u := by
  rw [scale, rapidity_eq_log_sub hu hv, ← Real.exp_add]
  have h : (Real.log u + Real.log v) / 2 +
      -((Real.log v - Real.log u) / 2) = Real.log u := by ring
  rw [h, Real.exp_log hu]

theorem two_scale_mul_cosh (hu : 0 < u) (hv : 0 < v) :
    2 * scale u v * Real.cosh (rapidity u v) = u + v := by
  calc
    2 * scale u v * Real.cosh (rapidity u v) =
        scale u v * Real.exp (rapidity u v) +
          scale u v * Real.exp (-rapidity u v) := by
      rw [Real.cosh_eq]
      ring
    _ = u + v := by
      rw [scale_mul_exp_rapidity hu hv, scale_mul_exp_neg_rapidity hu hv]
      ring

theorem two_scale_mul_sinh (hu : 0 < u) (hv : 0 < v) :
    2 * scale u v * Real.sinh (rapidity u v) = v - u := by
  calc
    2 * scale u v * Real.sinh (rapidity u v) =
        scale u v * Real.exp (rapidity u v) -
          scale u v * Real.exp (-rapidity u v) := by
      rw [Real.sinh_eq]
      ring
    _ = v - u := by
      rw [scale_mul_exp_rapidity hu hv, scale_mul_exp_neg_rapidity hu hv]

theorem cosh_rapidity (hu : 0 < u) (hv : 0 < v) :
    Real.cosh (rapidity u v) = (u + v) / (2 * scale u v) := by
  apply (eq_div_iff (ne_of_gt (mul_pos (by norm_num) (scale_pos u v)))).2
  calc
    Real.cosh (rapidity u v) * (2 * scale u v) =
        2 * scale u v * Real.cosh (rapidity u v) := by ring
    _ = u + v := two_scale_mul_cosh hu hv

theorem sinh_rapidity (hu : 0 < u) (hv : 0 < v) :
    Real.sinh (rapidity u v) = (v - u) / (2 * scale u v) := by
  apply (eq_div_iff (ne_of_gt (mul_pos (by norm_num) (scale_pos u v)))).2
  calc
    Real.sinh (rapidity u v) * (2 * scale u v) =
        2 * scale u v * Real.sinh (rapidity u v) := by ring
    _ = v - u := two_scale_mul_sinh hu hv

theorem tanh_rapidity_eq_difference_ratio (hu : 0 < u) (hv : 0 < v) :
    Real.tanh (rapidity u v) = (v - u) / (u + v) := by
  rw [Real.tanh_eq_sinh_div_cosh, sinh_rapidity hu hv, cosh_rapidity hu hv]
  field_simp [ne_of_gt (scale_pos u v), ne_of_gt (add_pos hu hv)]

theorem sech_rapidity_eq_overlap (hu : 0 < u) (hv : 0 < v) :
    sechProfile (rapidity u v) = overlap u v := by
  rw [sechProfile, cosh_rapidity hu hv, one_div_div]
  rw [overlap, sqrt_product_eq_scale hu hv]

theorem overlap_pos (hu : 0 < u) (hv : 0 < v) :
    0 < overlap u v := by
  rw [← sech_rapidity_eq_overlap hu hv, sechProfile]
  exact div_pos (by norm_num) (Real.cosh_pos _)

theorem overlap_le_one (hu : 0 < u) (hv : 0 < v) :
    overlap u v ≤ 1 := by
  unfold overlap
  apply (div_le_one (add_pos hu hv)).2
  have hs := Real.sq_sqrt (le_of_lt (mul_pos hu hv))
  have hn := Real.sqrt_nonneg (u * v)
  nlinarith [sq_nonneg (u - v)]

theorem overlap_sq (hu : 0 < u) (hv : 0 < v) :
    overlap u v ^ 2 = 4 * (u * v) / (u + v) ^ 2 := by
  dsimp [overlap]
  rw [div_pow, mul_pow, Real.sq_sqrt (le_of_lt (mul_pos hu hv))]
  norm_num

/-- Null-to-Cartesian conversion in an auxiliary Lorentz plane. -/
theorem lorentz_quadratic_identity (u v : ℝ) :
    ((u + v) / 2) ^ 2 - ((v - u) / 2) ^ 2 = u * v := by
  ring

/-- Opposite exponential rescalings preserve the product of the null coordinates. -/
theorem boost_preserves_product (u v theta : ℝ) :
    (u * Real.exp (-theta)) * (v * Real.exp theta) = u * v := by
  have h : Real.exp (-theta) * Real.exp theta = 1 := by
    rw [← Real.exp_add]
    simp
  calc
    (u * Real.exp (-theta)) * (v * Real.exp theta) =
        (u * v) * (Real.exp (-theta) * Real.exp theta) := by ring
    _ = u * v := by rw [h, mul_one]

/-- The same rescaling translates rapidity; no spacetime interpretation is assumed. -/
theorem rapidity_boost (hu : 0 < u) (hv : 0 < v) (theta : ℝ) :
    rapidity (u * Real.exp (-theta)) (v * Real.exp theta) =
      rapidity u v + theta := by
  rw [rapidity_eq_log_sub (mul_pos hu (Real.exp_pos _))
      (mul_pos hv (Real.exp_pos _)), rapidity_eq_log_sub hu hv]
  rw [Real.log_mul (ne_of_gt hv) (Real.exp_ne_zero _),
    Real.log_mul (ne_of_gt hu) (Real.exp_ne_zero _), Real.log_exp, Real.log_exp]
  ring

end InfoGeometry.Nuclear.FocalRapidity
