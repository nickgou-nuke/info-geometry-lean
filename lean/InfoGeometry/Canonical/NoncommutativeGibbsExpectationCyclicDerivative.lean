import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecificLimits.Normed
import InfoGeometry.Canonical.NoncommutativeGibbsExpectationBridge
import InfoGeometry.Optics.OperatorQGTFrechetChernCharacter

/-!
# Cyclic derivative of the noncommutative Gibbs partition function

The preceding Gibbs expectation owner proves two complementary facts:

* the trace of the Bochner--Duhamel insertion is
  `Tr (exp H * T)` for arbitrary, possibly noncommuting, `H` and `T`;
* the actual changed-origin Fréchet derivative of the traced exponential has
  that value on commuting directions.

This file closes the remaining trace-level edge for arbitrary directions.  It
reuses the repository theorem

`finiteOperatorTrace_powerDerivative`

which cyclically collapses every insertion in the noncommutative derivative of
`A ^ k`.  Termwise differentiation of the scalar exponential series then gives

`D (H ↦ Tr (exp H))_H[T] = Tr (exp H * T)`

without identifying the operator-valued changed-origin derivative with the
Duhamel operator.  The two derivatives are proved equal only after applying the
finite trace, which is exactly the strength required by the Gibbs expectation
theorem.

No commutativity hypothesis, diagonalization, axiom, or supplied derivative is
used.
-/

noncomputable section
set_option autoImplicit false

namespace InfoGeometry.Canonical.NoncommutativeGibbsExpectationBridge

open scoped BigOperators
open InfoGeometry.OperatorAlgebra
open InfoGeometry.Optics.OperatorQGTFrechetChernCharacter
open SouriauOnsagerBKM

/-! ## 1. Scalar exponential-series terms and their exact derivatives -/

/-- The `k`th scalar term in the traced exponential along the affine operator
line `H + z T`. -/
noncomputable def tracedExponentialSeriesTerm
    {n : ℕ} (H T : Operator n) (k : ℕ) (z : ℂ) : ℂ :=
  ((Nat.factorial k : ℂ)⁻¹) *
    finiteOperatorTrace ((H + z • T) ^ k)

/-- The cyclically reduced derivative of the `k`th traced exponential term.
The zeroth term has zero derivative; the successor term is the preceding
factorial coefficient times `Tr (T (H + zT)^k)`. -/
noncomputable def tracedExponentialSeriesTermDerivative
    {n : ℕ} (H T : Operator n) : ℕ → ℂ → ℂ
  | 0, _ => 0
  | k + 1, z =>
      ((Nat.factorial k : ℂ)⁻¹) *
        finiteOperatorTrace (T * (H + z • T) ^ k)

private theorem inv_factorial_succ_mul_succ_natCast (k : ℕ) :
    ((Nat.factorial (k + 1) : ℂ)⁻¹) * ((k + 1 : ℕ) : ℂ) =
      (Nat.factorial k : ℂ)⁻¹ := by
  rw [Nat.factorial_succ, Nat.cast_mul]
  have hk : (((k + 1 : ℕ) : ℂ)) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero k
  have hf : ((Nat.factorial k : ℂ)) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero k
  field_simp [hk, hf]

/-- Every scalar term has the derivative obtained by cyclically reducing the
repository-owned noncommutative power derivative. -/
theorem hasDerivAt_tracedExponentialSeriesTerm
    {n : ℕ} (H T : Operator n) (k : ℕ) (z : ℂ) :
    HasDerivAt
      (tracedExponentialSeriesTerm H T k)
      (tracedExponentialSeriesTermDerivative H T k z) z := by
  cases k with
  | zero =>
      simpa [tracedExponentialSeriesTerm,
        tracedExponentialSeriesTermDerivative] using
        (hasDerivAt_const (x := z)
          (c := finiteOperatorTrace (1 : Operator n)))
  | succ k =>
      have hLine :
          HasDerivAt (fun w : ℂ => H + w • T) T z := by
        convert
          (hasDerivAt_const (x := z) H).add
            ((hasDerivAt_id (x := z)).smul_const T) using 1 <;>
          simp
      have hPowerRaw :
          HasDerivAt
            (fun w : ℂ => finiteOperatorTrace ((H + w • T) ^ (k + 1)))
            (frechetChernCharacterDerivative n (k + 1)
              (H + z • T) T) z := by
        simpa [frechetChernCharacter, Function.comp_def] using
          (hasFDerivAt_frechetChernCharacter n (k + 1)
            (H + z • T)).comp_hasDerivAt_of_eq z hLine (by simp)
      have hPower :
          HasDerivAt
            (fun w : ℂ => finiteOperatorTrace ((H + w • T) ^ (k + 1)))
            (((k + 1 : ℕ) : ℂ) *
              finiteOperatorTrace (T * (H + z • T) ^ k)) z := by
        rw [frechetChernCharacterDerivative_eq] at hPowerRaw
        simpa using hPowerRaw
      change HasDerivAt
        (fun w : ℂ =>
          ((Nat.factorial (k + 1) : ℂ)⁻¹) *
            finiteOperatorTrace ((H + w • T) ^ (k + 1)))
        (((Nat.factorial k : ℂ)⁻¹) *
          finiteOperatorTrace (T * (H + z • T) ^ k)) z
      have hScaled :=
        hPower.const_mul ((Nat.factorial (k + 1) : ℂ)⁻¹)
      rw [← mul_assoc, inv_factorial_succ_mul_succ_natCast] at hScaled
      exact hScaled

/-! ## 2. A uniform summable derivative majorant on the unit disk -/

/-- A scalar majorant for all term derivatives on `‖z‖ < 1`. -/
noncomputable def tracedExponentialDerivativeMajorant
    {n : ℕ} (H T : Operator n) : ℕ → ℝ
  | 0 => 0
  | k + 1 =>
      (‖finiteOperatorTraceCLM n‖ * ‖T‖) *
        ((‖H‖ + ‖T‖) ^ k / (Nat.factorial k : ℝ))

/-- The derivative majorant is summable, by the ordinary scalar exponential
series. -/
theorem summable_tracedExponentialDerivativeMajorant
    {n : ℕ} (H T : Operator n) :
    Summable (tracedExponentialDerivativeMajorant H T) := by
  apply (summable_nat_add_iff 1).mp
  simpa [tracedExponentialDerivativeMajorant] using
    (Real.summable_pow_div_factorial (‖H‖ + ‖T‖)).mul_left
      (‖finiteOperatorTraceCLM n‖ * ‖T‖)

/-- Uniform norm bound for the scalar term derivatives on the complex unit
disk. -/
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
      have hzNorm : ‖z‖ ≤ 1 := by
        have hzlt : ‖z‖ < 1 := by
          simpa [Metric.mem_ball] using hz
        exact hzlt.le
      have hBase :
          ‖H + z • T‖ ≤ ‖H‖ + ‖T‖ := by
        calc
          ‖H + z • T‖ ≤ ‖H‖ + ‖z • T‖ := norm_add_le _ _
          _ = ‖H‖ + ‖z‖ * ‖T‖ := by rw [norm_smul]
          _ ≤ ‖H‖ + 1 * ‖T‖ := by gcongr
          _ = ‖H‖ + ‖T‖ := by rw [one_mul]
      have hPower :
          ‖(H + z • T) ^ k‖ ≤ (‖H‖ + ‖T‖) ^ k := by
        calc
          ‖(H + z • T) ^ k‖ ≤ ‖H + z • T‖ ^ k := norm_pow_le _ _
          _ ≤ (‖H‖ + ‖T‖) ^ k := by gcongr
      have hMul :
          ‖T * (H + z • T) ^ k‖ ≤
            ‖T‖ * (‖H‖ + ‖T‖) ^ k := by
        calc
          ‖T * (H + z • T) ^ k‖ ≤
              ‖T‖ * ‖(H + z • T) ^ k‖ := norm_mul_le _ _
          _ ≤ ‖T‖ * (‖H‖ + ‖T‖) ^ k := by gcongr
      have hTrace :
          ‖finiteOperatorTrace (T * (H + z • T) ^ k)‖ ≤
            ‖finiteOperatorTraceCLM n‖ *
              (‖T‖ * (‖H‖ + ‖T‖) ^ k) := by
        calc
          ‖finiteOperatorTrace (T * (H + z • T) ^ k)‖ =
              ‖finiteOperatorTraceCLM n
                (T * (H + z • T) ^ k)‖ := rfl
          _ ≤ ‖finiteOperatorTraceCLM n‖ *
              ‖T * (H + z • T) ^ k‖ :=
                (finiteOperatorTraceCLM n).le_opNorm _
          _ ≤ ‖finiteOperatorTraceCLM n‖ *
              (‖T‖ * (‖H‖ + ‖T‖) ^ k) := by
                gcongr
      change
        ‖((Nat.factorial k : ℂ)⁻¹) *
          finiteOperatorTrace (T * (H + z • T) ^ k)‖ ≤
        (‖finiteOperatorTraceCLM n‖ * ‖T‖) *
          ((‖H‖ + ‖T‖) ^ k / (Nat.factorial k : ℝ))
      rw [norm_mul, norm_inv, RCLike.norm_natCast]
      calc
        (Nat.factorial k : ℝ)⁻¹ *
            ‖finiteOperatorTrace (T * (H + z • T) ^ k)‖ ≤
          (Nat.factorial k : ℝ)⁻¹ *
            (‖finiteOperatorTraceCLM n‖ *
              (‖T‖ * (‖H‖ + ‖T‖) ^ k)) := by
                gcongr
        _ = (‖finiteOperatorTraceCLM n‖ * ‖T‖) *
            ((‖H‖ + ‖T‖) ^ k / (Nat.factorial k : ℝ)) := by
              ring

/-! ## 3. The traced exponential is the sum of these scalar terms -/

/-- Summability of the scalar traced-exponential series at the base point of
the affine line. -/
theorem summable_tracedExponentialSeriesTerm_zero
    {n : ℕ} (H T : Operator n) :
    Summable (fun k : ℕ => tracedExponentialSeriesTerm H T k 0) := by
  let f : ℕ → Operator n := fun k =>
    ((Nat.factorial k : ℂ)⁻¹) • H ^ k
  have hf : Summable f := by
    simpa [f] using
      (NormedSpace.expSeries_summable' (𝕂 := ℂ) H)
  have hTrace :
      Summable (fun k : ℕ => finiteOperatorTraceCLM n (f k)) :=
    (finiteOperatorTraceCLM n).summable hf
  simpa [tracedExponentialSeriesTerm, f,
    finiteOperatorTrace_complex_smul] using hTrace

/-- The partition line is exactly the scalar sum of the traced exponential
series. -/
theorem partitionLine_eq_tsum_tracedExponentialSeriesTerm
    {n : ℕ} (H T : Operator n) (z : ℂ) :
    partitionLine H T z =
      ∑' k : ℕ, tracedExponentialSeriesTerm H T k z := by
  let A : Operator n := H + z • T
  have hs :
      Summable (fun k : ℕ =>
        ((Nat.factorial k : ℂ)⁻¹) • A ^ k) := by
    simpa using (NormedSpace.expSeries_summable' (𝕂 := ℂ) A)
  unfold partitionLine tracedExponential
  rw [NormedSpace.exp_eq_tsum ℂ]
  change finiteOperatorTraceCLM n
      (∑' k : ℕ, ((Nat.factorial k : ℂ)⁻¹) • A ^ k) =
    ∑' k : ℕ,
      ((Nat.factorial k : ℂ)⁻¹) * finiteOperatorTrace (A ^ k)
  rw [(finiteOperatorTraceCLM n).map_tsum hs]
  apply tsum_congr
  intro k
  simpa using
    finiteOperatorTrace_complex_smul
      ((Nat.factorial k : ℂ)⁻¹) (A ^ k)

/-! ## 4. Cyclic summation of the derivative series -/

/-- The derivative series sums to the ordinary first-moment numerator. -/
theorem tsum_tracedExponentialSeriesTermDerivative_zero
    {n : ℕ} (H T : Operator n) :
    (∑' k : ℕ, tracedExponentialSeriesTermDerivative H T k 0) =
      finiteOperatorTrace (NormedSpace.exp H * T) := by
  have hzero : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by simp
  have hMajorant :=
    summable_tracedExponentialDerivativeMajorant H T
  have hDerivative :
      Summable
        (fun k : ℕ =>
          tracedExponentialSeriesTermDerivative H T k 0) :=
    Summable.of_norm_bounded hMajorant
      (fun k =>
        norm_tracedExponentialSeriesTermDerivative_le H T k 0 hzero)
  have hExp :
      HasSum
        (fun k : ℕ => ((Nat.factorial k : ℂ)⁻¹) • H ^ k)
        (NormedSpace.exp H) := by
    simpa [NormedSpace.expSeries_apply_eq] using
      (NormedSpace.expSeries_hasSum_exp (𝕂 := ℂ) H)
  have hTrace :
      HasSum
        (fun k : ℕ =>
          ((Nat.factorial k : ℂ)⁻¹) *
            finiteOperatorTrace (T * H ^ k))
        (finiteOperatorTrace (T * NormedSpace.exp H)) := by
    simpa [mul_smul_comm, finiteOperatorTrace_complex_smul] using
      ((hExp.mul_left T).mapL (finiteOperatorTraceCLM n))
  calc
    (∑' k : ℕ, tracedExponentialSeriesTermDerivative H T k 0) =
        tracedExponentialSeriesTermDerivative H T 0 0 +
          ∑' k : ℕ,
            tracedExponentialSeriesTermDerivative H T (k + 1) 0 :=
      hDerivative.tsum_eq_zero_add
    _ = ∑' k : ℕ,
        ((Nat.factorial k : ℂ)⁻¹) *
          finiteOperatorTrace (T * H ^ k) := by
            simp [tracedExponentialSeriesTermDerivative]
    _ = finiteOperatorTrace (T * NormedSpace.exp H) := hTrace.tsum_eq
    _ = finiteOperatorTrace (NormedSpace.exp H * T) :=
      finiteOperatorTrace_mul_comm _ _

/-! ## 5. Full arbitrary-direction derivative and Gibbs expectation -/

/-- The partition line has the expected derivative for every operator
direction, without a commutation hypothesis. -/
theorem hasDerivAt_partitionLine
    {n : ℕ} (H T : Operator n) :
    HasDerivAt (partitionLine H T)
      (finiteOperatorTrace (NormedSpace.exp H * T)) 0 := by
  have hSeries :
      HasDerivAt
        (fun z : ℂ =>
          ∑' k : ℕ, tracedExponentialSeriesTerm H T k z)
        (∑' k : ℕ,
          tracedExponentialSeriesTermDerivative H T k 0) 0 := by
    exact hasDerivAt_tsum_of_isPreconnected
      (u := tracedExponentialDerivativeMajorant H T)
      (t := Metric.ball (0 : ℂ) 1)
      (summable_tracedExponentialDerivativeMajorant H T)
      Metric.isOpen_ball Metric.isPreconnected_ball
      (fun k z _hz =>
        hasDerivAt_tracedExponentialSeriesTerm H T k z)
      (fun k z hz =>
        norm_tracedExponentialSeriesTermDerivative_le H T k z hz)
      (by simp)
      (summable_tracedExponentialSeriesTerm_zero H T)
      (by simp)
  rw [tsum_tracedExponentialSeriesTermDerivative_zero H T] at hSeries
  have hFunction :
      partitionLine H T =
        fun z : ℂ =>
          ∑' k : ℕ, tracedExponentialSeriesTerm H T k z := by
    funext z
    exact partitionLine_eq_tsum_tracedExponentialSeriesTerm H T z
  rw [hFunction]
  exact hSeries

/-- The repository's changed-origin Fréchet derivative has the cyclic
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
the same finite trace in every noncommuting direction.  No operator-level
equality is claimed. -/
theorem finiteOperatorTrace_exponentialDerivative_eq_duhamelDerivative
    {n : ℕ} (H T : Operator n) :
    finiteOperatorTrace
        (exponentialDerivative (𝕜 := ℂ) H T) =
      finiteOperatorTrace (duhamelDerivative H T) := by
  change tracedExponentialDerivative H T =
    finiteOperatorTrace (duhamelDerivative H T)
  rw [tracedExponentialDerivative_apply,
    finiteOperatorTrace_duhamelDerivative]

/-- Full noncommutative operator expectation theorem:

`d/dz log Tr(exp(H + zT)) |_{z=0} = Tr(ρ_H T)`.

Only the principal-log branch condition is required. -/
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

/-- Four-channel noncommutative expectation theorem.  Pairwise commutativity
of the sufficient statistics is no longer required. -/
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
