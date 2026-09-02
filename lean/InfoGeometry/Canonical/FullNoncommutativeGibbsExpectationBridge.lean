import InfoGeometry.Canonical.NoncommutativeGibbsExpectationBridge
import InfoGeometry.Canonical.TracedExponentialCyclicDerivative

/-!
# Full finite noncommutative Gibbs expectation theorem

This owner closes the remaining trace-level calculus edge left explicit in
`NoncommutativeGibbsExpectationBridge`.

The operator exponential derivative itself is kept in Mathlib's changed-origin
power-series representation.  The separate cyclic-series owner proves that,
after applying the finite trace, its value in every tangent direction `T` is
`Tr (exp H * T)`.  Hence no commutativity of the sufficient statistics is
needed for the first derivative of the finite log-partition function.

No operator-level equality between the changed-origin derivative and the
real Bochner--Duhamel derivative is asserted; their traces are proved equal,
which is exactly the invariant required by Gibbs expectation geometry.
-/

noncomputable section
set_option autoImplicit false

namespace InfoGeometry.Canonical.NoncommutativeGibbsExpectationBridge

open InfoGeometry.OperatorAlgebra
open SouriauOnsagerBKM
open InfoGeometry.Canonical.TracedExponentialCyclicDerivative

/-! ## Trace-level identification of the two derivative presentations -/

/-- The changed-origin Frechet derivative of the traced exponential has the
ordinary first-moment numerator in every tangent direction. -/
theorem tracedExponentialDerivative_apply
    {n : ℕ} (H T : Operator n) :
    tracedExponentialDerivative H T =
      finiteOperatorTrace (NormedSpace.exp H * T) := by
  change finiteOperatorTrace
      (exponentialDerivative (𝕜 := ℂ) H T) = _
  exact finiteOperatorTrace_exponentialDerivative H T

/-- Trace-level equality between Mathlib's changed-origin derivative and the
Bochner--Duhamel derivative. -/
theorem finiteOperatorTrace_exponentialDerivative_eq_duhamelDerivative
    {n : ℕ} (H T : Operator n) :
    finiteOperatorTrace
        (exponentialDerivative (𝕜 := ℂ) H T) =
      finiteOperatorTrace (duhamelDerivative H T) := by
  rw [finiteOperatorTrace_exponentialDerivative,
    finiteOperatorTrace_duhamelDerivative]

/-! ## Full Frechet derivative of the finite log-partition function -/

/-- Principal-branch finite log-partition potential on the whole operator
algebra. -/
noncomputable def logTracedExponential
    {n : ℕ} (H : Operator n) : ℂ :=
  Complex.log (tracedExponential H)

/-- Native Frechet derivative of the finite log-partition potential. -/
noncomputable def logTracedExponentialDerivative
    {n : ℕ} (H : Operator n) : Operator n →L[ℂ] ℂ :=
  (tracedExponential H)⁻¹ • tracedExponentialDerivative H

/-- Genuine Frechet differentiability of the finite noncommutative
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
normalized Gibbs expectation, without a commutativity hypothesis. -/
theorem logTracedExponentialDerivative_apply_eq_expectation
    {n : ℕ} (H T : Operator n) :
    logTracedExponentialDerivative H T =
      operatorExpectation H T := by
  simp only [logTracedExponentialDerivative,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [tracedExponentialDerivative_apply,
    operatorExpectation_eq_trace_div]
  simp [div_eq_mul_inv, mul_comm]

/-- The native `fderiv` of the finite log-partition is exactly the expectation
functional. -/
theorem fderiv_logTracedExponential
    {n : ℕ} (H : Operator n)
    (hSlit : tracedExponential H ∈ Complex.slitPlane) :
    fderiv ℂ logTracedExponential H =
      logTracedExponentialDerivative H :=
  (hasFDerivAt_logTracedExponential H hSlit).fderiv

/-! ## Arbitrary operator directions -/

/-- Derivative of the finite partition line in an arbitrary, possibly
noncommuting, operator direction. -/
theorem hasDerivAt_partitionLine
    {n : ℕ} (H T : Operator n) :
    HasDerivAt (partitionLine H T)
      (finiteOperatorTrace (NormedSpace.exp H * T)) 0 := by
  simpa [partitionLine, tracedExponential] using
    hasDerivAt_finiteOperatorTrace_exp_line H T

/-- Full finite noncommutative operator expectation theorem:

`d/dz log Tr(exp(H + zT)) |_{z=0} = Tr(ρ_H T)`.

Only the principal-log branch condition remains; `H` and `T` need not
commute. -/
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

/-! ## Four-channel operator exponential families -/

/-- Full four-channel expectation theorem.  Pairwise commutation of the
sufficient statistics is not required. -/
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

/-- The earlier commuting-family theorem is recovered immediately from the
full noncommutative statement. -/
theorem hasDerivAt_fourOperatorLogPartitionCoordinate_eq_expectation_of_pairwiseCommute
    {n : ℕ} (T : Fin 4 → Operator n)
    (_hComm : PairwiseCommuteFour T)
    (theta : FourComplexParameters) (mu : Fin 4)
    (hSlit : fourOperatorPartition T theta ∈ Complex.slitPlane) :
    HasDerivAt
      (fourOperatorLogPartitionCoordinate T theta mu)
      (fourOperatorExpectation T theta mu) 0 :=
  hasDerivAt_fourOperatorLogPartitionCoordinate_eq_expectation_noncommutative
    T theta mu hSlit

end InfoGeometry.Canonical.NoncommutativeGibbsExpectationBridge
