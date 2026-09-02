import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.SpecificLimits.Normed
import InfoGeometry.Canonical.NoncommutativeGibbsExpectationBridge
import InfoGeometry.Optics.OperatorQGTFrechetChernCharacter

/-!
# Full cyclic derivative of the noncommutative Gibbs partition function

The base Gibbs owner proves the unconditional trace collapse of the genuine
Bochner--Duhamel insertion and constructs the changed-origin Frechet
derivative of the finite traced exponential.  This owner closes the remaining
trace-level edge for arbitrary, possibly noncommuting, operator directions.

The proof reuses the repository theorem
`finiteOperatorTrace_powerDerivative`, which cyclically collapses every
insertion in the derivative of `A ^ k`.  Mathlib's local termwise
series-differentiation theorem, together with a factorial majorant on a bounded
complex line, then gives

`D (H ↦ Tr (exp H))_H[T] = Tr (exp H * T)`.

Consequently the principal-branch finite log-partition has a genuine Frechet
derivative whose evaluation in every tangent direction is the normalized
operator expectation.  No commutativity assumption, diagonalization, axiom,
`sorry`, or supplied derivative is introduced.

The changed-origin exponential derivative and the real Bochner--Duhamel
operator are identified only after application of the finite trace.  The
stronger operator equality is neither needed nor asserted.
-/

noncomputable section
set_option autoImplicit false

namespace InfoGeometry.Canonical.NoncommutativeGibbsExpectationBridge

open scoped BigOperators
open InfoGeometry.OperatorAlgebra
open InfoGeometry.Optics.OperatorQGTFrechetChernCharacter
open SouriauOnsagerBKM

/-! ## 1. Scalar exponential-series terms and exact derivatives -/

/-- The `k`th scalar term in the traced exponential along `H + z T`. -/
noncomputable def tracedExponentialSeriesTerm
    {n : ℕ} (H T : Operator n) (k : ℕ) (z : ℂ) : ℂ :=
  ((k.factorial : ℂ)⁻¹) *
    finiteOperatorTrace ((H + z • T) ^ k)

/-- The cyclically reduced derivative of the `k`th traced exponential term. -/
noncomputable def tracedExponentialSeriesTermDerivative
    {n : ℕ} (H T : Operator n) (k : ℕ) (z : ℂ) : ℂ :=
  ((k.factorial : ℂ)⁻¹) *
    ((k : ℂ) *
      finiteOperatorTrace
        (T * (H + z • T) ^ k.pred))

private theorem inverse_factorial_succ_mul_cast_succ (k : ℕ) :
    (((k + 1).factorial : ℂ)⁻¹) * (k + 1 : ℂ) =
      ((k.factorial : ℂ)⁻¹) := by
  rw [Nat.factorial_succ, Nat.cast_mul]
  have hk : ((k + 1 : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero k
  have hkfac : ((k.factorial : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero k
  field_simp [hk, hkfac]

@[simp] theorem tracedExponentialSeriesTermDerivative_zero
    {n : ℕ} (H T : Operator n) (z : ℂ) :
    tracedExponentialSeriesTermDerivative H T 0 z = 0 := by
  simp [tracedExponentialSeriesTermDerivative]

@[simp] theorem tracedExponentialSeriesTermDerivative_succ
    {n : ℕ} (H T : Operator n) (k : ℕ) (z : ℂ) :
    tracedExponentialSeriesTermDerivative H T (k + 1) z =
      ((k.factorial : ℂ)⁻¹) *
        finiteOperatorTrace (T * (H + z • T) ^ k) := by
  simp only [tracedExponentialSeriesTermDerivative, Nat.pred_succ]
  rw [← mul_assoc, inverse_factorial_succ_mul_cast_succ]

/-- Every scalar term has the derivative obtained by cyclically reducing the
repository-owned noncommutative power derivative. -/
theorem hasDerivAt_tracedExponentialSeriesTerm
    {n : ℕ} (H T : Operator n) (k : ℕ) (z : ℂ) :
    HasDerivAt
      (tracedExponentialSeriesTerm H T k)
      (tracedExponentialSeriesTermDerivative H T k z) z := by
  have hLine :
      HasDerivAt (fun w : ℂ => H + w • T) T z := by
    convert
      (hasDerivAt_const (x := z) H).add
        ((hasDerivAt_id (x := z)).smul_const T) using 1 <;>
      simp
  have hPower :
      HasDerivAt
        (fun w : ℂ =>
          frechetChernCharacter n k (H + w • T))
        (frechetChernCharacterDerivative n k
          (H + z • T) T) z := by
    simpa [Function.comp_def] using
      (hasFDerivAt_frechetChernCharacter n k
        (H + z • T)).comp_hasDerivAt_of_eq
          z hLine (by simp)
  rw [frechetChernCharacterDerivative_eq] at hPower
  simpa [tracedExponentialSeriesTerm,
    tracedExponentialSeriesTermDerivative,
    frechetChernCharacter, Function.comp_def] using
      hPower.const_mul ((k.factorial : ℂ)⁻¹)

/-! ## 2. Local factorial majorant -/

/-- Uniform norm radius for `H + zT` on the unit disk. -/
noncomputable def tracedExponentialLineRadius
    {n : ℕ} (H T : Operator n) : ℝ :=
  ‖H‖ + ‖T‖

/-- A factor covering the zeroth power without requiring a `NormOneClass`
instance on the operator ring. -/
noncomputable def tracedExponentialPowerNormConstant (n : ℕ) : ℝ :=
  max 1 ‖(1 : Operator n)‖

/-- Constant part of the derivative majorant. -/
noncomputable def tracedExponentialDerivativeConstant
    (n : ℕ) (T : Operator n) : ℝ :=
  ‖finiteOperatorTraceCLM n‖ * ‖T‖ *
    tracedExponentialPowerNormConstant n

/-- Factorial majorant for the derivative series. -/
noncomputable def tracedExponentialDerivativeMajorant
    {n : ℕ} (H T : Operator n) : ℕ → ℝ
  | 0 => 0
  | k + 1 =>
      tracedExponentialDerivativeConstant n T *
        (tracedExponentialLineRadius H T) ^ k /
          (k.factorial : ℝ)

/-- The derivative majorant is summable. -/
theorem summable_tracedExponentialDerivativeMajorant
    {n : ℕ} (H T : Operator n) :
    Summable (tracedExponentialDerivativeMajorant H T) := by
  refine (summable_nat_add_iff 1).mp ?_
  simpa [tracedExponentialDerivativeMajorant] using
    (Real.summable_pow_div_factorial
      (tracedExponentialLineRadius H T)).mul_left
        (tracedExponentialDerivativeConstant n T)

private theorem norm_affine_operator_le_lineRadius
    {n : ℕ} (H T : Operator n) (z : ℂ)
    (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    ‖H + z • T‖ ≤ tracedExponentialLineRadius H T := by
  have hzNorm : ‖z‖ ≤ 1 := by
    have hzlt : ‖z‖ < 1 := by
      simpa [dist_eq] using (Metric.mem_ball.mp hz)
    exact hzlt.le
  calc
    ‖H + z • T‖ ≤ ‖H‖ + ‖z • T‖ := norm_add_le _ _
    _ = ‖H‖ + ‖z‖ * ‖T‖ := by rw [norm_smul]
    _ ≤ ‖H‖ + 1 * ‖T‖ := by
      exact add_le_add_left
        (mul_le_mul_of_nonneg_right hzNorm (norm_nonneg T)) _
    _ = tracedExponentialLineRadius H T := by
      simp [tracedExponentialLineRadius]

private theorem norm_affine_operator_pow_le
    {n : ℕ} (H T : Operator n) (z : ℂ)
    (hz : z ∈ Metric.ball (0 : ℂ) 1) (k : ℕ) :
    ‖(H + z • T) ^ k‖ ≤
      tracedExponentialPowerNormConstant n *
        (tracedExponentialLineRadius H T) ^ k := by
  cases k with
  | zero =>
      simpa [tracedExponentialPowerNormConstant] using
        (le_max_right (1 : ℝ) ‖(1 : Operator n)‖)
  | succ k =>
      calc
        ‖(H + z • T) ^ (k + 1)‖ ≤
            ‖H + z • T‖ ^ (k + 1) :=
          norm_pow_le' _ (Nat.succ_pos k)
        _ ≤ (tracedExponentialLineRadius H T) ^ (k + 1) := by
          exact pow_le_pow_left₀
            (norm_nonneg (H + z • T))
            (norm_affine_operator_le_lineRadius H T z hz) _
        _ = 1 * (tracedExponentialLineRadius H T) ^ (k + 1) := by
          rw [one_mul]
        _ ≤ tracedExponentialPowerNormConstant n *
            (tracedExponentialLineRadius H T) ^ (k + 1) := by
          exact mul_le_mul_of_nonneg_right
            (le_max_left (1 : ℝ) ‖(1 : Operator n)‖)
            (pow_nonneg
              (add_nonneg (norm_nonneg H) (norm_nonneg T)) _)

private theorem norm_trace_mul_affine_pow_le
    {n : ℕ} (H T : Operator n) (z : ℂ)
    (hz : z ∈ Metric.ball (0 : ℂ) 1) (k : ℕ) :
    ‖finiteOperatorTrace (T * (H + z • T) ^ k)‖ ≤
      tracedExponentialDerivativeConstant n T *
        (tracedExponentialLineRadius H T) ^ k := by
  calc
    ‖finiteOperatorTrace (T * (H + z • T) ^ k)‖ ≤
        ‖finiteOperatorTraceCLM n‖ *
          ‖T * (H + z • T) ^ k‖ := by
      change ‖finiteOperatorTraceCLM n
        (T * (H + z • T) ^ k)‖ ≤ _
      exact (finiteOperatorTraceCLM n).le_opNorm _
    _ ≤ ‖finiteOperatorTraceCLM n‖ *
        (‖T‖ * ‖(H + z • T) ^ k‖) := by
      exact mul_le_mul_of_nonneg_left
        (norm_mul_le T ((H + z • T) ^ k))
        (norm_nonneg (finiteOperatorTraceCLM n))
    _ ≤ ‖finiteOperatorTraceCLM n‖ *
        (‖T‖ *
          (tracedExponentialPowerNormConstant n *
            (tracedExponentialLineRadius H T) ^ k)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (norm_affine_operator_pow_le H T z hz k)
          (norm_nonneg T))
        (norm_nonneg (finiteOperatorTraceCLM n))
    _ = tracedExponentialDerivativeConstant n T *
        (tracedExponentialLineRadius H T) ^ k := by
      simp [tracedExponentialDerivativeConstant]
      ring

/-- Uniform derivative bound on the unit complex disk. -/
theorem norm_tracedExponentialSeriesTermDerivative_le
    {n : ℕ} (H T : Operator n) (k : ℕ) (z : ℂ)
    (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    ‖tracedExponentialSeriesTermDerivative H T k z‖ ≤
      tracedExponentialDerivativeMajorant H T k := by
  cases k with
  | zero =>
      simp [tracedExponentialSeriesTermDerivative,
        tracedExponentialDerivativeMajorant]
  | succ k =>
      rw [tracedExponentialSeriesTermDerivative_succ]
      change
        ‖((k.factorial : ℂ)⁻¹) *
          finiteOperatorTrace (T * (H + z • T) ^ k)‖ ≤
        tracedExponentialDerivativeConstant n T *
          (tracedExponentialLineRadius H T) ^ k /
            (k.factorial : ℝ)
      rw [norm_mul, norm_inv, RCLike.norm_natCast]
      calc
        ((k.factorial : ℝ)⁻¹) *
            ‖finiteOperatorTrace (T * (H + z • T) ^ k)‖ ≤
          ((k.factorial : ℝ)⁻¹) *
            (tracedExponentialDerivativeConstant n T *
              (tracedExponentialLineRadius H T) ^ k) := by
            exact mul_le_mul_of_nonneg_left
              (norm_trace_mul_affine_pow_le H T z hz k)
              (by positivity)
        _ = tracedExponentialDerivativeConstant n T *
            (tracedExponentialLineRadius H T) ^ k /
              (k.factorial : ℝ) := by
            rw [div_eq_mul_inv]
            ring

/-! ## 3. Summation and cyclic coefficient collapse -/

/-- The traced terms are summable at the center of the affine line. -/
theorem summable_tracedExponentialSeriesTerm_zero
    {n : ℕ} (H T : Operator n) :
    Summable (fun k : ℕ => tracedExponentialSeriesTerm H T k 0) := by
  have hExp :
      Summable (fun k : ℕ =>
        ((k.factorial : ℂ)⁻¹) • H ^ k) :=
    NormedSpace.expSeries_summable' (𝕂 := ℂ) H
  have hTrace := (finiteOperatorTraceCLM n).summable hExp
  simpa [tracedExponentialSeriesTerm,
    finiteOperatorTrace_complex_smul, smul_eq_mul] using hTrace

/-- The partition line is exactly the scalar sum of the traced exponential
series. -/
theorem partitionLine_eq_tsum_tracedExponentialSeriesTerm
    {n : ℕ} (H T : Operator n) (z : ℂ) :
    partitionLine H T z =
      ∑' k : ℕ, tracedExponentialSeriesTerm H T k z := by
  let A : Operator n := H + z • T
  have hExp :
      Summable (fun k : ℕ =>
        ((k.factorial : ℂ)⁻¹) • A ^ k) :=
    NormedSpace.expSeries_summable' (𝕂 := ℂ) A
  unfold partitionLine tracedExponential
  rw [NormedSpace.exp_eq_tsum ℂ]
  change finiteOperatorTraceCLM n
      (∑' k : ℕ, ((k.factorial : ℂ)⁻¹) • A ^ k) =
    ∑' k : ℕ,
      ((k.factorial : ℂ)⁻¹) * finiteOperatorTrace (A ^ k)
  rw [(finiteOperatorTraceCLM n).map_tsum hExp]
  apply tsum_congr
  intro k
  simpa using
    finiteOperatorTrace_complex_smul
      ((k.factorial : ℂ)⁻¹) (A ^ k)

/-- The derivative series is summable at the center. -/
theorem summable_tracedExponentialSeriesTermDerivative_zero
    {n : ℕ} (H T : Operator n) :
    Summable
      (fun k : ℕ =>
        tracedExponentialSeriesTermDerivative H T k 0) := by
  apply Summable.of_norm_bounded
    (f := fun k : ℕ =>
      tracedExponentialSeriesTermDerivative H T k 0)
    (g := tracedExponentialDerivativeMajorant H T)
  · exact summable_tracedExponentialDerivativeMajorant H T
  · intro k
    exact norm_tracedExponentialSeriesTermDerivative_le
      H T k 0 (Metric.mem_ball_self (by norm_num))

/-- The derivative series sums to the ordinary first-moment numerator. -/
theorem tsum_tracedExponentialSeriesTermDerivative_zero
    {n : ℕ} (H T : Operator n) :
    (∑' k : ℕ,
      tracedExponentialSeriesTermDerivative H T k 0) =
        finiteOperatorTrace (NormedSpace.exp H * T) := by
  have hDerivativeSummable :=
    summable_tracedExponentialSeriesTermDerivative_zero H T
  have hExp :
      HasSum
        (fun k : ℕ => ((k.factorial : ℂ)⁻¹) • H ^ k)
        (NormedSpace.exp H) :=
    NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) H
  have hLeft :
      HasSum
        (fun k : ℕ =>
          T * (((k.factorial : ℂ)⁻¹) • H ^ k))
        (T * NormedSpace.exp H) :=
    hExp.mul_left T
  have hTrace := hLeft.mapL (finiteOperatorTraceCLM n)
  have hTraceSeries :
      HasSum
        (fun k : ℕ =>
          ((k.factorial : ℂ)⁻¹) *
            finiteOperatorTrace (T * H ^ k))
        (finiteOperatorTrace (T * NormedSpace.exp H)) := by
    simpa [finiteOperatorTrace_complex_smul,
      smul_eq_mul, mul_smul_comm] using hTrace
  calc
    (∑' k : ℕ,
      tracedExponentialSeriesTermDerivative H T k 0) =
        tracedExponentialSeriesTermDerivative H T 0 0 +
          ∑' k : ℕ,
            tracedExponentialSeriesTermDerivative H T (k + 1) 0 :=
      tsum_eq_zero_add' hDerivativeSummable
    _ = ∑' k : ℕ,
        ((k.factorial : ℂ)⁻¹) *
          finiteOperatorTrace (T * H ^ k) := by
      rw [tracedExponentialSeriesTermDerivative_zero, zero_add]
      apply tsum_congr
      intro k
      simp
    _ = finiteOperatorTrace (T * NormedSpace.exp H) :=
      hTraceSeries.tsum_eq
    _ = finiteOperatorTrace (NormedSpace.exp H * T) :=
      finiteOperatorTrace_mul_comm _ _

/-! ## 4. Full arbitrary-direction derivative -/

/-- Termwise differentiation of the scalar traced exponential series. -/
theorem hasDerivAt_tsum_tracedExponentialSeriesTerm
    {n : ℕ} (H T : Operator n) :
    HasDerivAt
      (fun z : ℂ =>
        ∑' k : ℕ, tracedExponentialSeriesTerm H T k z)
      (∑' k : ℕ,
        tracedExponentialSeriesTermDerivative H T k 0) 0 := by
  exact hasDerivAt_tsum_of_isPreconnected
    (u := tracedExponentialDerivativeMajorant H T)
    (t := Metric.ball (0 : ℂ) 1)
    (y₀ := (0 : ℂ))
    (y := (0 : ℂ))
    (summable_tracedExponentialDerivativeMajorant H T)
    Metric.isOpen_ball
    Metric.isPreconnected_ball
    (fun k z _hz => hasDerivAt_tracedExponentialSeriesTerm H T k z)
    (fun k z hz =>
      norm_tracedExponentialSeriesTermDerivative_le H T k z hz)
    (Metric.mem_ball_self (by norm_num))
    (summable_tracedExponentialSeriesTerm_zero H T)
    (Metric.mem_ball_self (by norm_num))

/-- The partition line has the expected derivative in every operator
direction. -/
theorem hasDerivAt_partitionLine
    {n : ℕ} (H T : Operator n) :
    HasDerivAt (partitionLine H T)
      (finiteOperatorTrace (NormedSpace.exp H * T)) 0 := by
  have hSeries := hasDerivAt_tsum_tracedExponentialSeriesTerm H T
  rw [tsum_tracedExponentialSeriesTermDerivative_zero H T] at hSeries
  have hFunction :
      partitionLine H T =
        fun z : ℂ =>
          ∑' k : ℕ, tracedExponentialSeriesTerm H T k z := by
    funext z
    exact partitionLine_eq_tsum_tracedExponentialSeriesTerm H T z
  rw [hFunction]
  exact hSeries

/-- The repository's changed-origin Frechet derivative has the cyclic
first-moment trace in every direction. -/
theorem tracedExponentialDerivative_apply
    {n : ℕ} (H T : Operator n) :
    tracedExponentialDerivative H T =
      finiteOperatorTrace (NormedSpace.exp H * T) := by
  have hLine :
      HasDerivAt (fun z : ℂ => H + z • T) T 0 := by
    convert
      (hasDerivAt_const (x := (0 : ℂ)) H).add
        ((hasDerivAt_id (x := (0 : ℂ))).smul_const T) using 1 <;>
      simp
  have hFromFrechet :
      HasDerivAt (partitionLine H T)
        (tracedExponentialDerivative H T) 0 := by
    simpa [partitionLine, Function.comp_def] using
      (hasFDerivAt_tracedExponential H).comp_hasDerivAt_of_eq
        (0 : ℂ) hLine (by simp)
  exact hFromFrechet.unique (hasDerivAt_partitionLine H T)

/-- The changed-origin exponential derivative and the Duhamel derivative have
the same finite trace in every noncommuting direction. -/
theorem finiteOperatorTrace_exponentialDerivative_eq_duhamelDerivative
    {n : ℕ} (H T : Operator n) :
    finiteOperatorTrace
        (exponentialDerivative (𝕜 := ℂ) H T) =
      finiteOperatorTrace (duhamelDerivative H T) := by
  change tracedExponentialDerivative H T =
    finiteOperatorTrace (duhamelDerivative H T)
  rw [tracedExponentialDerivative_apply,
    finiteOperatorTrace_duhamelDerivative]

/-! ## 5. Full Frechet log-partition and Gibbs expectation -/

/-- Principal-branch finite log-partition potential on the whole operator
algebra. -/
noncomputable def logTracedExponential
    {n : ℕ} (H : Operator n) : ℂ :=
  Complex.log (tracedExponential H)

/-- Native Frechet derivative of the finite log-partition potential. -/
noncomputable def logTracedExponentialDerivative
    {n : ℕ} (H : Operator n) : Operator n →L[ℂ] ℂ :=
  (tracedExponential H)⁻¹ • tracedExponentialDerivative H

/-- Genuine Frechet differentiability of the full finite noncommutative
log-partition function on the principal logarithm branch. -/
theorem hasFDerivAt_logTracedExponential
    {n : ℕ} (H : Operator n)
    (hSlit : tracedExponential H ∈ Complex.slitPlane) :
    HasFDerivAt logTracedExponential
      (logTracedExponentialDerivative H) H := by
  simpa [logTracedExponential,
    logTracedExponentialDerivative] using
      (hasFDerivAt_tracedExponential H).clog hSlit

/-- Every tangent evaluation of the log-partition Frechet derivative is the
normalized Gibbs expectation. -/
theorem logTracedExponentialDerivative_apply_eq_expectation
    {n : ℕ} (H T : Operator n) :
    logTracedExponentialDerivative H T =
      operatorExpectation H T := by
  simp only [logTracedExponentialDerivative,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [tracedExponentialDerivative_apply,
    operatorExpectation_eq_trace_div]
  simp [div_eq_mul_inv, mul_comm]

/-- The native `fderiv` of the finite log-partition is the expectation
functional. -/
theorem fderiv_logTracedExponential
    {n : ℕ} (H : Operator n)
    (hSlit : tracedExponential H ∈ Complex.slitPlane) :
    fderiv ℂ logTracedExponential H =
      logTracedExponentialDerivative H :=
  (hasFDerivAt_logTracedExponential H hSlit).fderiv

/-- Full noncommutative operator expectation theorem on an arbitrary tangent
line.  Only the principal-log branch condition is required. -/
theorem hasDerivAt_logPartitionLine_eq_expectation
    {n : ℕ} (H T : Operator n)
    (hSlit : tracedExponential H ∈ Complex.slitPlane) :
    HasDerivAt (logPartitionLine H T)
      (operatorExpectation H T) 0 := by
  have hPartition := hasDerivAt_partitionLine H T
  have hLog := hPartition.clog (by
    simpa [partitionLine] using hSlit)
  rw [operatorExpectation_eq_trace_div]
  simpa [logPartitionLine, partitionLine] using hLog

/-- Four-channel noncommutative expectation theorem. Pairwise commutativity of
the sufficient statistics is not required. -/
theorem hasDerivAt_fourOperatorLogPartitionCoordinate_eq_expectation_noncommutative
    {n : ℕ} (T : Fin 4 → Operator n)
    (theta : FourComplexParameters) (mu : Fin 4)
    (hSlit : fourOperatorPartition T theta ∈ Complex.slitPlane) :
    HasDerivAt
      (fourOperatorLogPartitionCoordinate T theta mu)
      (fourOperatorExpectation T theta mu) 0 := by
  simpa [fourOperatorLogPartitionCoordinate,
    fourOperatorExpectation, fourOperatorPartition,
    logPartitionLine, partitionLine] using
    hasDerivAt_logPartitionLine_eq_expectation
      (fourOperatorExponent T theta) (T mu) hSlit

end InfoGeometry.Canonical.NoncommutativeGibbsExpectationBridge
