import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic
import InfoGeometry.Canonical.SouriauOnsagerBKMIntegrability
import InfoGeometry.OperatorAlgebra.NoncommutativePowerDerivative
import InfoGeometry.OperatorAlgebra.NoncommutativeDuhamelDerivative

/-!
# Noncommutative Gibbs expectation bridge

This owner separates two analytic statements that are often conflated.

First, for the genuine Bochner--Duhamel operator

`D exp_H[T] = ∫₀¹ exp((1-t)H) T exp(tH) dt`,

cyclicity of the finite operator trace collapses the ordered integral without
any commutativity assumption:

`Tr(D exp_H[T]) = Tr(exp(H) T)`.

Second, the repository already owns the genuine changed-origin Fréchet
derivative of `NormedSpace.exp`.  On a direction commuting with the base
operator, that derivative agrees with ordinary multiplication by `exp(H)`.
This gives an actual `HasDerivAt` theorem for the complex log-partition and the
normalized operator expectation.

The remaining fully noncommutative edge is intentionally not hidden: one still
needs a trace-level identification between the changed-origin exponential
Fréchet derivative and the Duhamel operator for an arbitrary noncommuting
direction.  No hypothesis wrapper, axiom, or `sorry` is introduced here.
-/

noncomputable section
set_option autoImplicit false

namespace InfoGeometry.Canonical.NoncommutativeGibbsExpectationBridge

open MeasureTheory
open scoped Interval BigOperators
open InfoGeometry.OperatorAlgebra
open SouriauOnsagerBKM

abbrev Operator (n : ℕ) := FiniteOperatorAlgebra n
abbrev FourComplexParameters := Fin 4 → ℂ

/-! ## 1. Trace as a real continuous linear map -/

/-- The native finite operator trace, restricted from complex to real scalars
for transport through the real-parameter Duhamel integral. -/
noncomputable def finiteOperatorTraceRealCLM (n : ℕ) :
    Operator n →L[ℝ] ℂ :=
  (finiteOperatorTraceCLM n).restrictScalars ℝ

@[simp] theorem finiteOperatorTraceRealCLM_apply
    {n : ℕ} (A : Operator n) :
    finiteOperatorTraceRealCLM n A = finiteOperatorTrace A :=
  rfl

/-- Complex scalar multiplication may be pulled through the finite trace. -/
theorem finiteOperatorTrace_complex_smul
    {n : ℕ} (c : ℂ) (A : Operator n) :
    finiteOperatorTrace (c • A) = c * finiteOperatorTrace A := by
  change finiteOperatorTraceLinear n (c • A) =
    c * finiteOperatorTraceLinear n A
  rw [map_smul]
  rfl

/-! ## 2. Cyclic collapse of the noncommutative Duhamel integral -/

/-- Pointwise trace collapse of the ordered Duhamel integrand.  The inserted
operator `T` need not commute with `H`. -/
theorem finiteOperatorTrace_duhamelIntegrand
    {n : ℕ} (H T : Operator n) (t : ℝ) :
    finiteOperatorTrace
        (NormedSpace.exp ((1 - t) • H) * T *
          NormedSpace.exp (t • H)) =
      finiteOperatorTrace (NormedSpace.exp H * T) := by
  letI : NormedAlgebra ℚ (Operator n) :=
    NormedAlgebra.restrictScalars ℚ ℝ (Operator n)
  have hComm : Commute (t • H) ((1 - t) • H) :=
    ((Commute.refl H).smul_left t).smul_right (1 - t)
  have hSum : t • H + (1 - t) • H = H := by
    module
  calc
    finiteOperatorTrace
        (NormedSpace.exp ((1 - t) • H) * T *
          NormedSpace.exp (t • H)) =
      finiteOperatorTrace
        (NormedSpace.exp (t • H) *
          (NormedSpace.exp ((1 - t) • H) * T)) :=
        finiteOperatorTrace_mul_comm _ _
    _ = finiteOperatorTrace
        ((NormedSpace.exp (t • H) *
          NormedSpace.exp ((1 - t) • H)) * T) := by
          rw [mul_assoc]
    _ = finiteOperatorTrace
        (NormedSpace.exp (t • H + (1 - t) • H) * T) := by
          rw [NormedSpace.exp_add_of_commute hComm]
    _ = finiteOperatorTrace (NormedSpace.exp H * T) := by
          rw [hSum]

/-- Continuity, hence interval integrability, of the evaluated Duhamel
integrand. -/
theorem intervalIntegrable_duhamelOperatorIntegrand
    {n : ℕ} (H T : Operator n) :
    IntervalIntegrable
      (fun t : ℝ =>
        NormedSpace.exp ((1 - t) • H) * T *
          NormedSpace.exp (t • H))
      volume 0 1 := by
  have hContinuous :
      Continuous
        (fun t : ℝ =>
          NormedSpace.exp ((1 - t) • H) * T *
            NormedSpace.exp (t • H)) := by
    letI : NormedAlgebra ℚ (Operator n) :=
      NormedAlgebra.restrictScalars ℚ ℝ (Operator n)
    fun_prop
  exact hContinuous.intervalIntegrable 0 1

/-- The trace of the genuine noncommutative Duhamel derivative is the ordinary
first-moment numerator.  This is unconditional in the inserted operator `T`. -/
theorem finiteOperatorTrace_duhamelDerivative
    {n : ℕ} (H T : Operator n) :
    finiteOperatorTrace (duhamelDerivative H T) =
      finiteOperatorTrace (NormedSpace.exp H * T) := by
  rw [duhamelDerivative_apply_integral]
  have hIntegrable := intervalIntegrable_duhamelOperatorIntegrand H T
  calc
    finiteOperatorTrace
        (∫ t in (0 : ℝ)..1,
          NormedSpace.exp ((1 - t) • H) * T *
            NormedSpace.exp (t • H)) =
      ∫ t in (0 : ℝ)..1,
        finiteOperatorTrace
          (NormedSpace.exp ((1 - t) • H) * T *
            NormedSpace.exp (t • H)) := by
          change finiteOperatorTraceRealCLM n
              (∫ t in (0 : ℝ)..1,
                NormedSpace.exp ((1 - t) • H) * T *
                  NormedSpace.exp (t • H)) = _
          symm
          exact ContinuousLinearMap.intervalIntegral_comp_comm
            (finiteOperatorTraceRealCLM n) hIntegrable
    _ = ∫ t in (0 : ℝ)..1,
        finiteOperatorTrace (NormedSpace.exp H * T) := by
          apply intervalIntegral.integral_congr
          intro t ht
          exact finiteOperatorTrace_duhamelIntegrand H T t
    _ = finiteOperatorTrace (NormedSpace.exp H * T) := by
          simp

/-! ## 3. Genuine Fréchet derivative of the traced exponential -/

/-- Finite traced operator exponential. -/
noncomputable def tracedExponential {n : ℕ} (H : Operator n) : ℂ :=
  finiteOperatorTrace (NormedSpace.exp H)

/-- Its genuine changed-origin Fréchet derivative, obtained by composing the
repository-owned noncommutative exponential derivative with the continuous
finite trace. -/
noncomputable def tracedExponentialDerivative
    {n : ℕ} (H : Operator n) : Operator n →L[ℂ] ℂ :=
  (finiteOperatorTraceCLM n).comp
    (exponentialDerivative (𝕜 := ℂ) H)

/-- Genuine complex Fréchet differentiability of the finite traced
exponential. -/
theorem hasFDerivAt_tracedExponential
    {n : ℕ} (H : Operator n) :
    HasFDerivAt tracedExponential
      (tracedExponentialDerivative H) H := by
  simpa [tracedExponential, tracedExponentialDerivative] using
    (finiteOperatorTraceCLM n).hasFDerivAt.comp H
      (hasFDerivAt_exp_noncommutative
        (𝕜 := ℂ) (A := Operator n) H)

/-! ## 4. Commuting-direction identification -/

/-- Complex-scalar version of the centralizer readout: on a direction that
commutes with the base operator, the genuine changed-origin derivative is
left multiplication by `exp(H)`. -/
theorem exponentialDerivative_apply_of_commute_complex
    {n : ℕ} (H T : Operator n) (hComm : Commute T H) :
    exponentialDerivative (𝕜 := ℂ) H T =
      NormedSpace.exp H * T := by
  letI : NormedAlgebra ℚ (Operator n) :=
    NormedAlgebra.restrictScalars ℚ ℂ (Operator n)
  have hLine :
      HasDerivAt (fun z : ℂ => H + z • T) T 0 := by
    convert
      (hasDerivAt_const (x := (0 : ℂ)) H).add
        ((hasDerivAt_id (x := (0 : ℂ))).smul_const T) using 1 <;>
      simp
  have hFromFrechet :
      HasDerivAt
        (fun z : ℂ => NormedSpace.exp (H + z • T))
        (exponentialDerivative (𝕜 := ℂ) H T) 0 := by
    convert
      (hasFDerivAt_exp_noncommutative
        (𝕜 := ℂ) (A := Operator n) H).comp_hasDerivAt_of_eq
          (x := (0 : ℂ)) (y := H) hLine (by simp) using 1 <;>
      simp [Function.comp_def]
  have hFactored :
      (fun z : ℂ => NormedSpace.exp (H + z • T)) =
        fun z : ℂ =>
          NormedSpace.exp H * NormedSpace.exp (z • T) := by
    funext z
    exact NormedSpace.exp_add_of_commute
      (hComm.symm.smul_right z)
  have hFromFactorization :
      HasDerivAt
        (fun z : ℂ => NormedSpace.exp (H + z • T))
        (NormedSpace.exp H * T) 0 := by
    rw [hFactored]
    simpa using
      (hasDerivAt_exp_smul_const T (0 : ℂ)).const_mul
        (NormedSpace.exp H)
  exact hFromFrechet.unique hFromFactorization

/-- The traced Fréchet derivative has the expected first-moment numerator on
commuting directions. -/
theorem tracedExponentialDerivative_apply_of_commute
    {n : ℕ} (H T : Operator n) (hComm : Commute T H) :
    tracedExponentialDerivative H T =
      finiteOperatorTrace (NormedSpace.exp H * T) := by
  change finiteOperatorTrace
      (exponentialDerivative (𝕜 := ℂ) H T) = _
  rw [exponentialDerivative_apply_of_commute_complex H T hComm]

/-! ## 5. Normalized operator expectation -/

/-- Normalized exponential weight.  It is defined algebraically for every
`H`; nonvanishing or positivity of the partition function is imposed only when
a logarithmic branch theorem requires it. -/
noncomputable def normalizedExponential
    {n : ℕ} (H : Operator n) : Operator n :=
  (tracedExponential H)⁻¹ • NormedSpace.exp H

/-- Expectation of an operator in the normalized exponential weight. -/
noncomputable def operatorExpectation
    {n : ℕ} (H T : Operator n) : ℂ :=
  finiteOperatorTrace (normalizedExponential H * T)

/-- The normalized expectation is the trace numerator divided by the partition
function. -/
theorem operatorExpectation_eq_trace_div
    {n : ℕ} (H T : Operator n) :
    operatorExpectation H T =
      finiteOperatorTrace (NormedSpace.exp H * T) /
        tracedExponential H := by
  unfold operatorExpectation normalizedExponential
  rw [smul_mul_assoc, finiteOperatorTrace_complex_smul]
  simp [div_eq_mul_inv, mul_comm]

/-- The normalized Duhamel trace readout is already the ordinary normalized
operator expectation, with no commutativity assumption. -/
noncomputable def duhamelLogarithmicReadout
    {n : ℕ} (H T : Operator n) : ℂ :=
  (tracedExponential H)⁻¹ *
    finiteOperatorTrace (duhamelDerivative H T)

/-- Noncommutative trace magic: the normalized Duhamel insertion equals the
normalized Gibbs expectation. -/
theorem duhamelLogarithmicReadout_eq_operatorExpectation
    {n : ℕ} (H T : Operator n) :
    duhamelLogarithmicReadout H T = operatorExpectation H T := by
  unfold duhamelLogarithmicReadout
  rw [finiteOperatorTrace_duhamelDerivative,
    operatorExpectation_eq_trace_div]
  simp [div_eq_mul_inv, mul_comm]

/-! ## 6. Actual log-partition derivative on a commuting direction -/

/-- Partition function along one complex operator direction. -/
noncomputable def partitionLine
    {n : ℕ} (H T : Operator n) (z : ℂ) : ℂ :=
  tracedExponential (H + z • T)

/-- Principal-branch logarithmic potential along one operator direction. -/
noncomputable def logPartitionLine
    {n : ℕ} (H T : Operator n) (z : ℂ) : ℂ :=
  Complex.log (partitionLine H T z)

/-- Derivative of the partition line on a commuting direction. -/
theorem hasDerivAt_partitionLine_of_commute
    {n : ℕ} (H T : Operator n) (hComm : Commute T H) :
    HasDerivAt (partitionLine H T)
      (finiteOperatorTrace (NormedSpace.exp H * T)) 0 := by
  have hLine :
      HasDerivAt (fun z : ℂ => H + z • T) T 0 := by
    convert
      (hasDerivAt_const (x := (0 : ℂ)) H).add
        ((hasDerivAt_id (x := (0 : ℂ))).smul_const T) using 1 <;>
      simp
  have hComp :
      HasDerivAt (partitionLine H T)
        (tracedExponentialDerivative H T) 0 := by
    simpa [partitionLine, Function.comp_def] using
      (hasFDerivAt_tracedExponential H).comp_hasDerivAt_of_eq
        (0 : ℂ) hLine (by simp)
  rw [tracedExponentialDerivative_apply_of_commute H T hComm] at hComp
  exact hComp

/-- Operator expectation theorem on a commuting direction:

`d/dz log Tr(exp(H + zT)) |_{z=0} = Tr(ρ_H T)`.

The slit-plane premise is precisely the principal-log branch condition. -/
theorem hasDerivAt_logPartitionLine_eq_expectation_of_commute
    {n : ℕ} (H T : Operator n) (hComm : Commute T H)
    (hSlit : tracedExponential H ∈ Complex.slitPlane) :
    HasDerivAt (logPartitionLine H T)
      (operatorExpectation H T) 0 := by
  have hPartition := hasDerivAt_partitionLine_of_commute H T hComm
  have hLog := hPartition.clog (by
    simpa [partitionLine] using hSlit)
  rw [operatorExpectation_eq_trace_div]
  simpa [logPartitionLine, partitionLine] using hLog

/-! ## 7. Four-parameter commuting operator exponential families -/

/-- Four-channel operator exponent `K(θ) = Σ μ, θ_μ T_μ`. -/
noncomputable def fourOperatorExponent
    {n : ℕ} (T : Fin 4 → Operator n)
    (theta : FourComplexParameters) : Operator n :=
  ∑ mu : Fin 4, theta mu • T mu

/-- Pairwise commutation contract for a four-channel operator exponential
family. -/
def PairwiseCommuteFour
    {n : ℕ} (T : Fin 4 → Operator n) : Prop :=
  ∀ mu nu, Commute (T mu) (T nu)

/-- Every sufficient statistic commutes with the exponent when the four
statistics commute pairwise. -/
theorem sufficientStatistic_commutes_fourOperatorExponent
    {n : ℕ} (T : Fin 4 → Operator n)
    (hComm : PairwiseCommuteFour T)
    (theta : FourComplexParameters) (mu : Fin 4) :
    Commute (T mu) (fourOperatorExponent T theta) := by
  show T mu * (∑ nu : Fin 4, theta nu • T nu) =
    (∑ nu : Fin 4, theta nu • T nu) * T mu
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro nu hnu
  exact (hComm mu nu).smul_right (theta nu)

/-- Four-channel partition function. -/
noncomputable def fourOperatorPartition
    {n : ℕ} (T : Fin 4 → Operator n)
    (theta : FourComplexParameters) : ℂ :=
  tracedExponential (fourOperatorExponent T theta)

/-- Four-channel normalized Gibbs operator. -/
noncomputable def fourOperatorGibbsState
    {n : ℕ} (T : Fin 4 → Operator n)
    (theta : FourComplexParameters) : Operator n :=
  normalizedExponential (fourOperatorExponent T theta)

/-- Four-channel sufficient-statistic expectation. -/
noncomputable def fourOperatorExpectation
    {n : ℕ} (T : Fin 4 → Operator n)
    (theta : FourComplexParameters) (mu : Fin 4) : ℂ :=
  operatorExpectation (fourOperatorExponent T theta) (T mu)

/-- Coordinate log-partition path in the `mu` direction. -/
noncomputable def fourOperatorLogPartitionCoordinate
    {n : ℕ} (T : Fin 4 → Operator n)
    (theta : FourComplexParameters) (mu : Fin 4) (z : ℂ) : ℂ :=
  Complex.log
    (tracedExponential
      (fourOperatorExponent T theta + z • T mu))

/-- Actual coordinate expectation theorem for a commuting four-channel
operator exponential family. -/
theorem hasDerivAt_fourOperatorLogPartitionCoordinate_eq_expectation
    {n : ℕ} (T : Fin 4 → Operator n)
    (hComm : PairwiseCommuteFour T)
    (theta : FourComplexParameters) (mu : Fin 4)
    (hSlit : fourOperatorPartition T theta ∈ Complex.slitPlane) :
    HasDerivAt
      (fourOperatorLogPartitionCoordinate T theta mu)
      (fourOperatorExpectation T theta mu) 0 := by
  simpa [fourOperatorLogPartitionCoordinate,
    fourOperatorExpectation, fourOperatorPartition,
    logPartitionLine, partitionLine] using
    hasDerivAt_logPartitionLine_eq_expectation_of_commute
      (fourOperatorExponent T theta) (T mu)
      (sufficientStatistic_commutes_fourOperatorExponent T hComm theta mu)
      hSlit

end InfoGeometry.Canonical.NoncommutativeGibbsExpectationBridge
