import InfoGeometry.Analysis.BipolarCrossRatioLog
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Convex.SelfConcordantLogBarrier
import Mathlib.Tactic

/-!
# Bipolar logit coordinate versus the symmetric interval barrier

Two logarithmic functions were superimposed in the informal synthesis.
On `0 < x < 1` they are:

* the odd logit coordinate `log x - log (1-x)`;
* the even interval barrier `-log x - log (1-x)`.

They have the same distinguished midpoint but different differentials. The
logit has derivative `4` at `x = 1/2`, while the symmetric barrier has zero
first derivative and positive Hessian there. Thus the equation `eta = 0`
must not be confused with vanishing of the logarithmic-coordinate gradient.

The interval barrier is exactly the sum of two copies of the repository's
standard one-sided logarithmic barrier. This file proves the analytic and
Hadamard identities needed by the bipolar DAG; it does not identify either
function with entropy, free energy, or a force law.
-/

noncomputable section

namespace InfoGeometry.Convex.BipolarLogitBarrierDuality

open InfoGeometry.Analysis.BipolarCrossRatioLog
open InfoGeometry.Convex.SelfConcordantLogBarrier

/-- Left endpoint logarithmic barrier. -/
def leftSheetBarrier (x : ℝ) : ℝ := logBarrier x

/-- Right endpoint logarithmic barrier. -/
def rightSheetBarrier (x : ℝ) : ℝ := logBarrier (1 - x)

/-- Standard logarithmic barrier of the open unit interval. -/
def intervalBarrier (x : ℝ) : ℝ :=
  leftSheetBarrier x + rightSheetBarrier x

/-- Odd logarithmic odds coordinate on the open unit interval. -/
def logitCoordinate (x : ℝ) : ℝ :=
  Real.log x - Real.log (1 - x)

/-- Derivative readout of the logit coordinate. -/
def logitGradient (x : ℝ) : ℝ :=
  x⁻¹ + (1 - x)⁻¹

/-- Derivative readout of the symmetric interval barrier. -/
def intervalBarrierGradient (x : ℝ) : ℝ :=
  -x⁻¹ + (1 - x)⁻¹

/-- Hessian readout of the symmetric interval barrier. -/
def intervalBarrierHessian (x : ℝ) : ℝ :=
  1 / x ^ 2 + 1 / (1 - x) ^ 2

/-- The interval barrier is exactly a sum of two repository-owned standard
one-sided logarithmic barriers. -/
theorem intervalBarrier_eq_logBarrier_add_reflected (x : ℝ) :
    intervalBarrier x = logBarrier x + logBarrier (1 - x) := rfl

/-- The symmetric barrier is invariant under endpoint exchange. -/
theorem intervalBarrier_one_sub (x : ℝ) :
    intervalBarrier (1 - x) = intervalBarrier x := by
  simp [intervalBarrier, leftSheetBarrier, rightSheetBarrier, logBarrier]
  ring

/-- The logit coordinate changes sign under endpoint exchange. -/
theorem logitCoordinate_one_sub (x : ℝ) :
    logitCoordinate (1 - x) = -logitCoordinate x := by
  simp [logitCoordinate]

/-- Even/odd Hadamard readouts of the two endpoint barriers. -/
theorem barrier_logit_hadamard (x : ℝ) :
    intervalBarrier x = leftSheetBarrier x + rightSheetBarrier x ∧
      logitCoordinate x = rightSheetBarrier x - leftSheetBarrier x := by
  constructor
  · rfl
  · simp [logitCoordinate, leftSheetBarrier, rightSheetBarrier, logBarrier]
    ring

/-- Recovery of the two endpoint barriers from the even barrier and odd logit. -/
theorem sheetBarrier_recovery (x : ℝ) :
    leftSheetBarrier x = (intervalBarrier x - logitCoordinate x) / 2 ∧
      rightSheetBarrier x = (intervalBarrier x + logitCoordinate x) / 2 := by
  constructor <;>
    simp [intervalBarrier, logitCoordinate, leftSheetBarrier,
      rightSheetBarrier, logBarrier] <;>
    ring

/-- Genuine derivative of the left endpoint barrier. -/
theorem hasDerivAt_leftSheetBarrier
    {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt leftSheetBarrier (-x⁻¹) x := by
  unfold leftSheetBarrier logBarrier
  simpa using (Real.hasDerivAt_log hx).neg

/-- Genuine derivative of the right endpoint barrier. -/
theorem hasDerivAt_rightSheetBarrier
    {x : ℝ} (hx : 1 - x ≠ 0) :
    HasDerivAt rightSheetBarrier ((1 - x)⁻¹) x := by
  have hsub : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
    simpa using
      (hasDerivAt_const (x := x) (c := (1 : ℝ))).sub
        (hasDerivAt_id x)
  have hlog := (Real.hasDerivAt_log hx).comp x hsub
  unfold rightSheetBarrier logBarrier
  convert hlog.neg using 1 <;> ring

/-- Genuine derivative of the odd logit coordinate. -/
theorem hasDerivAt_logitCoordinate
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt logitCoordinate (logitGradient x) x := by
  have hx : x ≠ 0 := hx0.ne'
  have h1x : 1 - x ≠ 0 := (sub_pos.mpr hx1).ne'
  have hsub : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
    simpa using
      (hasDerivAt_const (x := x) (c := (1 : ℝ))).sub
        (hasDerivAt_id x)
  have hlogx := Real.hasDerivAt_log hx
  have hlog1x := (Real.hasDerivAt_log h1x).comp x hsub
  unfold logitCoordinate logitGradient
  convert hlogx.sub hlog1x using 1 <;> ring

/-- Genuine derivative of the symmetric interval barrier. -/
theorem hasDerivAt_intervalBarrier
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt intervalBarrier (intervalBarrierGradient x) x := by
  have hx : x ≠ 0 := hx0.ne'
  have h1x : 1 - x ≠ 0 := (sub_pos.mpr hx1).ne'
  simpa [intervalBarrier, intervalBarrierGradient] using
    (hasDerivAt_leftSheetBarrier hx).add
      (hasDerivAt_rightSheetBarrier h1x)

/-- Genuine derivative of the barrier gradient, hence the displayed Hessian is
an actual second-derivative readout. -/
theorem hasDerivAt_intervalBarrierGradient
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt intervalBarrierGradient (intervalBarrierHessian x) x := by
  have hx : x ≠ 0 := hx0.ne'
  have h1x : 1 - x ≠ 0 := (sub_pos.mpr hx1).ne'
  have hsub : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
    simpa using
      (hasDerivAt_const (x := x) (c := (1 : ℝ))).sub
        (hasDerivAt_id x)
  have hinv0 :
      HasDerivAt (fun y : ℝ => y⁻¹) (-(1 : ℝ) / x ^ 2) x := by
    convert (hasDerivAt_id x).inv hx using 1 <;> ring
  have hinv1 :
      HasDerivAt (fun y : ℝ => (1 - y)⁻¹)
        ((1 : ℝ) / (1 - x) ^ 2) x := by
    convert hsub.inv h1x using 1 <;> ring
  unfold intervalBarrierGradient intervalBarrierHessian
  convert hinv0.neg.add hinv1 using 1 <;> ring

/-- Strict positivity of the interval-barrier Hessian. -/
theorem intervalBarrierHessian_pos
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    0 < intervalBarrierHessian x := by
  unfold intervalBarrierHessian
  have hx2 : 0 < x ^ 2 := sq_pos_of_pos hx0
  have h1x2 : 0 < (1 - x) ^ 2 := sq_pos_of_pos (sub_pos.mpr hx1)
  positivity

/-- The logit coordinate vanishes at the midpoint. -/
@[simp] theorem logitCoordinate_half :
    logitCoordinate (1 / 2 : ℝ) = 0 := by
  norm_num [logitCoordinate]

/-- Its derivative does not vanish there. -/
@[simp] theorem logitGradient_half :
    logitGradient (1 / 2 : ℝ) = 4 := by
  norm_num [logitGradient]

/-- The symmetric barrier, unlike the logit, is stationary at the midpoint. -/
@[simp] theorem intervalBarrierGradient_half :
    intervalBarrierGradient (1 / 2 : ℝ) = 0 := by
  norm_num [intervalBarrierGradient]

/-- The symmetric barrier remains strictly curved at the midpoint. -/
@[simp] theorem intervalBarrierHessian_half :
    intervalBarrierHessian (1 / 2 : ℝ) = 8 := by
  norm_num [intervalBarrierHessian]

/-- On the open interval the symmetric barrier has its unique stationary point
at the midpoint. -/
theorem intervalBarrierGradient_eq_zero_iff
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    intervalBarrierGradient x = 0 ↔ x = 1 / 2 := by
  have hx : x ≠ 0 := hx0.ne'
  have h1x : 1 - x ≠ 0 := (sub_pos.mpr hx1).ne'
  constructor
  · intro h
    unfold intervalBarrierGradient at h
    field_simp [hx, h1x] at h
    linarith
  · intro h
    rw [h]
    exact intervalBarrierGradient_half

/-- Complement of the logistic coordinate. -/
theorem one_sub_logistic (t : ℝ) :
    1 - logistic t = 1 / (1 + Real.exp t) := by
  unfold logistic
  have hden : 1 + Real.exp t ≠ 0 := by positivity
  field_simp [hden]
  ring

/-- The real logistic map is the inverse of the logit coordinate. -/
theorem logitCoordinate_logistic (t : ℝ) :
    logitCoordinate (logistic t) = t := by
  have hsum : 1 + Real.exp t ≠ 0 := by positivity
  rw [logitCoordinate, one_sub_logistic]
  unfold logistic
  rw [Real.log_div (Real.exp_ne_zero t) hsum,
    Real.log_div one_ne_zero hsum, Real.log_exp, Real.log_one]
  ring

/-- The symmetric barrier in the logit coordinate is a two-sided log-sum-exp
potential, not the logit itself. -/
theorem intervalBarrier_logistic (t : ℝ) :
    intervalBarrier (logistic t) =
      2 * Real.log (1 + Real.exp t) - t := by
  have hsum : 1 + Real.exp t ≠ 0 := by positivity
  rw [intervalBarrier, leftSheetBarrier, rightSheetBarrier,
    logBarrier, one_sub_logistic]
  unfold logistic
  simp only [logBarrier]
  rw [Real.log_div (Real.exp_ne_zero t) hsum,
    Real.log_div one_ne_zero hsum, Real.log_exp, Real.log_one]
  ring

/-- The independently defined complex radial coordinate and the real logit
agree on the canonical logistic parameterization. -/
theorem logit_eq_eta_on_logistic (t : ℝ) :
    logitCoordinate (logistic t) = eta (logistic t : ℂ) := by
  rw [logitCoordinate_logistic, eta_logistic]

/-- Compact separation packet for the two logarithmic functions. -/
theorem bipolar_logit_barrier_duality_packet (t : ℝ) :
    logitCoordinate (1 / 2 : ℝ) = 0 ∧
      logitGradient (1 / 2 : ℝ) = 4 ∧
      intervalBarrierGradient (1 / 2 : ℝ) = 0 ∧
      intervalBarrierHessian (1 / 2 : ℝ) = 8 ∧
      logitCoordinate (logistic t) = t ∧
      intervalBarrier (logistic t) =
        2 * Real.log (1 + Real.exp t) - t := by
  exact ⟨logitCoordinate_half, logitGradient_half,
    intervalBarrierGradient_half, intervalBarrierHessian_half,
    logitCoordinate_logistic t, intervalBarrier_logistic t⟩

end InfoGeometry.Convex.BipolarLogitBarrierDuality
