import InfoGeometry.Dynamics.RindlerWedge
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Rindler lapse, stationary acceleration and clock normalization

Units are c = hbar = k_B = 1. `a` is the acceleration at x = 0; the
stationary observer at x has acceleration a / (1 + a*x). Physical statements
are restricted to a > 0 and positive lapse. This is coordinate calculus, not
an assumed Bisognano--Wichmann theorem or a semiconductor equivalence.
-/

namespace InfoGeometry.Geometry.RindlerLapseCalculus

noncomputable section

open InfoGeometry.Dynamics.RindlerWedge

def lapse (a x : ℝ) : ℝ := 1 + a * x
def radius (a x : ℝ) : ℝ := x + a⁻¹
def stationaryAcceleration (a x : ℝ) : ℝ := a / lapse a x

theorem hasDerivAt_lapse (a x : ℝ) : HasDerivAt (lapse a) a x := by
  simpa [lapse] using ((hasDerivAt_id x).const_mul a).const_add 1

theorem lapse_eq_mul_radius (a x : ℝ) (ha : a ≠ 0) :
    lapse a x = a * radius a x := by
  simp [lapse, radius, mul_add, ha, add_comm]

theorem radius_pos (a x : ℝ) (ha : 0 < a) (hx : 0 < lapse a x) :
    0 < radius a x := by
  rw [lapse_eq_mul_radius a x ha.ne'] at hx
  exact (mul_pos_iff_of_pos_left ha).mp hx

/-- Reuse the existing positive-radius Rindler carrier; its time is rapidity. -/
def toRindler (a x t : ℝ) (ha : 0 < a) (hx : 0 < lapse a x) :
    RindlerCoordinates :=
  ⟨(radius a x, a * t), radius_pos a x ha hx⟩

theorem lightcone_product (a x t : ℝ) (ha : 0 < a) (hx : 0 < lapse a x) :
    rindlerToMinkowski (toRindler a x t ha hx) 0 0 *
        rindlerToMinkowski (toRindler a x t ha hx) 1 0 = (radius a x) ^ 2 :=
  rindler_lightcone_product (toRindler a x t ha hx)

theorem hasDerivAt_log_lapse (a x : ℝ) (hx : lapse a x ≠ 0) :
    HasDerivAt (fun y => Real.log (lapse a y)) (stationaryAcceleration a x) x := by
  simpa [stationaryAcceleration] using (hasDerivAt_lapse a x).log hx

theorem hasDerivAt_stationaryAcceleration (a x : ℝ) (hx : lapse a x ≠ 0) :
    HasDerivAt (stationaryAcceleration a) (-(stationaryAcceleration a x) ^ 2) x := by
  convert (hasDerivAt_const x a).div (hasDerivAt_lapse a x) hx using 1 <;>
    simp [stationaryAcceleration, div_pow, pow_two] <;> ring

/-- Opposite signs distinguish support acceleration from the gravitational force convention. -/
theorem negative_log_gradient (a x : ℝ) (hx : lapse a x ≠ 0) :
    -(deriv (fun y => Real.log (lapse a y)) x) = -stationaryAcceleration a x := by
  rw [(hasDerivAt_log_lapse a x hx).deriv]

def minkowskiTime (a x t : ℝ) : ℝ := radius a x * Real.sinh (a * t)
def minkowskiPosition (a x t : ℝ) : ℝ := radius a x * Real.cosh (a * t)

theorem hasDerivAt_minkowskiTime (a x t : ℝ) (ha : a ≠ 0) :
    HasDerivAt (minkowskiTime a x) (lapse a x * Real.cosh (a * t)) t := by
  convert (((hasDerivAt_id t).const_mul a).sinh.const_mul (radius a x)) using 1 <;>
    simp [minkowskiTime, lapse_eq_mul_radius a x ha] <;> ring

theorem hasDerivAt_minkowskiPosition (a x t : ℝ) (ha : a ≠ 0) :
    HasDerivAt (minkowskiPosition a x) (lapse a x * Real.sinh (a * t)) t := by
  convert (((hasDerivAt_id t).const_mul a).cosh.const_mul (radius a x)) using 1 <;>
    simp [minkowskiPosition, lapse_eq_mul_radius a x ha] <;> ring

theorem hasDerivAt_minkowskiTime_space (a t x : ℝ) :
    HasDerivAt (fun y => minkowskiTime a y t) (Real.sinh (a * t)) x := by
  simpa [minkowskiTime, radius] using
    ((hasDerivAt_id x).add_const a⁻¹).mul_const (Real.sinh (a * t))

theorem hasDerivAt_minkowskiPosition_space (a t x : ℝ) :
    HasDerivAt (fun y => minkowskiPosition a y t) (Real.cosh (a * t)) x := by
  simpa [minkowskiPosition, radius] using
    ((hasDerivAt_id x).add_const a⁻¹).mul_const (Real.cosh (a * t))

/-- Exact pullback of the Minkowski quadratic line element by the computed Jacobian. -/
theorem minkowski_metric_pullback (a x t dt dx : ℝ) :
    -(lapse a x * Real.cosh (a * t) * dt + Real.sinh (a * t) * dx) ^ 2 +
      (lapse a x * Real.sinh (a * t) * dt + Real.cosh (a * t) * dx) ^ 2 =
    -(lapse a x) ^ 2 * dt ^ 2 + dx ^ 2 := by
  have h := Real.cosh_sq_sub_sinh_sq (a * t)
  calc
    _ = ((lapse a x) ^ 2 * dt ^ 2 - dx ^ 2) *
        (Real.sinh (a * t) ^ 2 - Real.cosh (a * t) ^ 2) := by ring
    _ = _ := by rw [show Real.sinh (a * t) ^ 2 - Real.cosh (a * t) ^ 2 = -1 by linarith]; ring

theorem jacobian_determinant (a x t : ℝ) :
    lapse a x * Real.cosh (a * t) * Real.cosh (a * t) -
      lapse a x * Real.sinh (a * t) * Real.sinh (a * t) = lapse a x := by
  calc
    _ = lapse a x * (Real.cosh (a * t) ^ 2 - Real.sinh (a * t) ^ 2) := by ring
    _ = _ := by rw [Real.cosh_sq_sub_sinh_sq]; ring

theorem hasDerivAt_velocity_time (r s : ℝ) :
    HasDerivAt (fun u => Real.cosh (u / r)) (Real.sinh (s / r) / r) s := by
  simpa [div_eq_mul_inv] using ((hasDerivAt_id s).div_const r).cosh

theorem hasDerivAt_velocity_space (r s : ℝ) :
    HasDerivAt (fun u => Real.sinh (u / r)) (Real.cosh (s / r) / r) s := by
  simpa [div_eq_mul_inv] using ((hasDerivAt_id s).div_const r).sinh

theorem hyperbola_velocity_norm (r s : ℝ) :
    -(Real.cosh (s / r)) ^ 2 + (Real.sinh (s / r)) ^ 2 = -1 := by
  linarith [Real.cosh_sq_sub_sinh_sq (s / r)]

/-- The unit future velocity and its proper-time derivative on a hyperbola. -/
theorem hyperbola_acceleration_norm (r s : ℝ) :
    -(Real.sinh (s / r) / r) ^ 2 + (Real.cosh (s / r) / r) ^ 2 = (r⁻¹) ^ 2 := by
  calc
    _ = (Real.cosh (s / r) ^ 2 - Real.sinh (s / r) ^ 2) / r ^ 2 := by ring
    _ = _ := by rw [Real.cosh_sq_sub_sinh_sq]; simp [div_pow]

/-- Nonzero proper acceleration excludes interpreting these stationary orbits as geodesics. -/
theorem hyperbola_acceleration_nonzero (r s : ℝ) (hr : 0 < r) :
    (Real.sinh (s / r) / r, Real.cosh (s / r) / r) ≠ (0, 0) := by
  intro h
  have h2 := congrArg Prod.snd h
  have hp : 0 < Real.cosh (s / r) / r := div_pos (Real.cosh_pos _) hr
  exact (ne_of_gt hp) h2

def localTemperature (T0 a x : ℝ) : ℝ := T0 / lapse a x

theorem tolman_product (T0 a x : ℝ) (hx : lapse a x ≠ 0) :
    localTemperature T0 a x * lapse a x = T0 := by
  exact div_mul_cancel₀ T0 hx

/-- Algebraic normalization selected by a 2*pi Euclidean angle, not a QFT KMS theorem. -/
def euclideanPeriod (a : ℝ) : ℝ := 2 * Real.pi / a

theorem euclidean_angle_period (a : ℝ) (ha : a ≠ 0) :
    a * euclideanPeriod a = 2 * Real.pi := by
  dsimp [euclideanPeriod]
  field_simp [ha]

theorem local_unruh_scale (a x : ℝ) :
    localTemperature (a / (2 * Real.pi)) a x =
      stationaryAcceleration a x / (2 * Real.pi) := by
  dsimp [localTemperature, stationaryAcceleration]
  ring

/-- Positive boost normalization. Tomita Delta^(is) may use the opposite orientation. -/
def positiveModularParameter (a t : ℝ) : ℝ := a * t / (2 * Real.pi)

theorem modular_rapidity_readback (a t : ℝ) :
    2 * Real.pi * positiveModularParameter a t = a * t := by
  dsimp [positiveModularParameter]
  have hp : (2 : ℝ) * Real.pi ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  field_simp [hp]

end
end InfoGeometry.Geometry.RindlerLapseCalculus
