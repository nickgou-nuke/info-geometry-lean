import InfoGeometry.Canonical.NoncommutativeGibbsExpectationCyclicDerivative
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Two-point Fréchet numerator for the noncommutative Gibbs Hessian

The first-moment owner proves the derivative of `Tr(exp H)` in every operator
direction after cyclic trace reduction.  The Hessian requires one stronger
scalar object: the derivative of

`H ↦ Tr(exp H * B)`

in a second direction `A`.

This file proves that derivative directly from the repository's genuine
changed-origin `exponentialDerivative`.  It does not identify the resulting
two-insertion trace with the Kubo--Mori interval integral; that is the one
remaining analytic edge needed to turn this exact Fréchet two-point response
into the centered BKM covariance owner.
-/

noncomputable section
set_option autoImplicit false

namespace InfoGeometry.Canonical.NoncommutativeGibbsTwoPointFrechetBridge

open SouriauOnsagerBKM
open InfoGeometry.OperatorAlgebra
open InfoGeometry.Canonical.NoncommutativeGibbsExpectationBridge

/-! The derivative of the first variation is exposed before any BKM
identification.  This keeps the analytic Hessian edge separated from the
later interval-integral comparison. -/

abbrev Operator (n : ℕ) := FiniteOperatorAlgebra n

/-- Continuous right multiplication on the finite operator algebra. -/
noncomputable def rightMulCLM {n : ℕ} (B : Operator n) :
    Operator n →L[ℂ] Operator n :=
  ContinuousLinearMap.mk (LinearMap.mulRight ℂ B)
    (LinearMap.continuous_of_finiteDimensional (LinearMap.mulRight ℂ B))

@[simp] theorem rightMulCLM_apply
    {n : ℕ} (B X : Operator n) :
    rightMulCLM B X = X * B :=
  rfl

/-- Trace after right multiplication by a fixed insertion. -/
noncomputable def tracedRightMulCLM {n : ℕ} (B : Operator n) :
    Operator n →L[ℂ] ℂ :=
  (finiteOperatorTraceCLM n).comp (rightMulCLM B)

@[simp] theorem tracedRightMulCLM_apply
    {n : ℕ} (B X : Operator n) :
    tracedRightMulCLM B X = finiteOperatorTrace (X * B) :=
  rfl

/-- Unnormalised two-point numerator `Tr(exp H * B)`. -/
noncomputable def twoPointNumerator {n : ℕ}
    (B H : Operator n) : ℂ :=
  finiteOperatorTrace (NormedSpace.exp H * B)

/-- Genuine Fréchet derivative of the two-point numerator. -/
noncomputable def twoPointNumeratorDerivative {n : ℕ}
    (H B : Operator n) : Operator n →L[ℂ] ℂ :=
  (tracedRightMulCLM B).comp
    (exponentialDerivative (𝕜 := ℂ) H)

@[simp] theorem twoPointNumeratorDerivative_apply
    {n : ℕ} (H A B : Operator n) :
    twoPointNumeratorDerivative H B A =
      finiteOperatorTrace
        (exponentialDerivative (𝕜 := ℂ) H A * B) :=
  rfl

/-- The two-point numerator has the actual changed-origin Fréchet derivative;
no commutativity assumption on `H`, `A`, or `B` is used. -/
theorem hasFDerivAt_twoPointNumerator
    {n : ℕ} (H B : Operator n) :
    HasFDerivAt (twoPointNumerator B)
      (twoPointNumeratorDerivative H B) H := by
  unfold twoPointNumerator twoPointNumeratorDerivative
  exact (tracedRightMulCLM B).hasFDerivAt.comp H
    (hasFDerivAt_exp_noncommutative (𝕜 := ℂ) H)

/-- Directional form along the affine line `H + z A`. -/
theorem hasDerivAt_twoPointNumeratorLine
    {n : ℕ} (H A B : Operator n) :
    HasDerivAt
      (fun z : ℂ => twoPointNumerator B (H + z • A))
      (finiteOperatorTrace
        (exponentialDerivative (𝕜 := ℂ) H A * B)) 0 := by
  have hLine :
      HasDerivAt (fun z : ℂ => H + z • A) A 0 := by
    convert
      (hasDerivAt_const (x := (0 : ℂ)) H).add
        ((hasDerivAt_id (x := (0 : ℂ))).smul_const A) using 1 <;>
      simp
  have harg : H + (0 : ℂ) • A = H := by
    rw [zero_smul ℂ A, add_zero]
  simpa using
    (hasFDerivAt_twoPointNumerator H B).comp_hasDerivAt_of_eq
      (0 : ℂ) hLine harg.symm

/-- Normalised first moment written as a scalar quotient. -/
noncomputable def normalizedTwoPointLine {n : ℕ}
    (H A B : Operator n) (z : ℂ) : ℂ :=
  twoPointNumerator B (H + z • A) /
    tracedExponential (H + z • A)

/-- Exact quotient-rule derivative of a Gibbs expectation before the
Kubo--Mori identification of the two-point numerator. -/
theorem hasDerivAt_normalizedTwoPointLine
    {n : ℕ} (H A B : Operator n)
    (hZ : tracedExponential H ≠ 0) :
    HasDerivAt (normalizedTwoPointLine H A B)
      ((finiteOperatorTrace
          (exponentialDerivative (𝕜 := ℂ) H A * B) *
          tracedExponential H -
        twoPointNumerator B H *
          finiteOperatorTrace (NormedSpace.exp H * A)) /
        (tracedExponential H) ^ 2) 0 := by
  have hNum := hasDerivAt_twoPointNumeratorLine H A B
  have hDen :=
    InfoGeometry.Canonical.NoncommutativeGibbsExpectationBridge.hasDerivAt_partitionLine
      H A
  have harg : H + (0 : ℂ) • A = H := by
    rw [zero_smul ℂ A, add_zero]
  unfold normalizedTwoPointLine
  convert hNum.div hDen (by
    change tracedExponential (H + (0 : ℂ) • A) ≠ 0
    rw [harg]
    exact hZ) using 1 <;>
    simp [partitionLine, twoPointNumerator, harg]

/-- The second-direction derivative of the normalized two-point response at
the base point.  This is the exact quotient-rule interface needed when the
first log-partition derivative is differentiated; no Hessian or BKM
identification is asserted here. -/
theorem deriv_normalizedTwoPointLine_at_zero
    {n : ℕ} (H A B : Operator n)
    (hZ : tracedExponential H ≠ 0) :
    deriv (normalizedTwoPointLine H A B) 0 =
      ((finiteOperatorTrace
          (exponentialDerivative (𝕜 := ℂ) H A * B) *
          tracedExponential H -
        twoPointNumerator B H *
          finiteOperatorTrace (NormedSpace.exp H * A)) /
        (tracedExponential H) ^ 2) := by
  exact (hasDerivAt_normalizedTwoPointLine H A B hZ).deriv

/-- The second directional variation of the finite log-partition gradient.

The function being differentiated is the first Fréchet derivative evaluated
on `B`, along the affine direction `A`.  Its derivative is therefore the
quotient-rule expression for the changed-origin two-point numerator.  This is
the exact finite-dimensional Hessian precursor; no commutativity or BKM
identification is assumed. -/
theorem hasDerivAt_logTracedExponentialDerivative_apply_line
    {n : ℕ} (H A B : Operator n)
    (hSlit : tracedExponential H ∈ Complex.slitPlane) :
    HasDerivAt
      (fun z : ℂ =>
        logTracedExponentialDerivative (H + z • A) B)
      ((finiteOperatorTrace
          (exponentialDerivative (𝕜 := ℂ) H A * B) *
          tracedExponential H -
        twoPointNumerator B H *
          finiteOperatorTrace (NormedSpace.exp H * A)) /
        (tracedExponential H) ^ 2) 0 := by
  have hZ : tracedExponential H ≠ 0 := by
    exact Complex.slitPlane_ne_zero hSlit
  have hBase := hasDerivAt_normalizedTwoPointLine H A B hZ
  have hEq :
      (fun z : ℂ =>
        logTracedExponentialDerivative (H + z • A) B) =
        normalizedTwoPointLine H A B := by
    funext z
    rw [logTracedExponentialDerivative_apply_eq_expectation]
    rw [operatorExpectation_eq_trace_div]
    rfl
  rw [hEq]
  exact hBase

/-- In a commuting direction, the exact second directional response reduces to
the ordinary exponential insertion.  This is the last algebraic simplification
before comparing the result with the BKM interval kernel. -/
theorem hasDerivAt_logTracedExponentialDerivative_apply_line_of_commute
    {n : ℕ} (H A B : Operator n)
    (hSlit : tracedExponential H ∈ Complex.slitPlane)
    (hComm : Commute H A) :
    HasDerivAt
      (fun z : ℂ =>
        logTracedExponentialDerivative (H + z • A) B)
      ((finiteOperatorTrace
          (NormedSpace.exp H * A * B) *
          tracedExponential H -
        finiteOperatorTrace (NormedSpace.exp H * B) *
          finiteOperatorTrace (NormedSpace.exp H * A)) /
        (tracedExponential H) ^ 2) 0 := by
  have h := hasDerivAt_logTracedExponentialDerivative_apply_line
    H A B hSlit
  rw [exponentialDerivative_apply_of_commute_complex H A hComm.symm]
    at h
  exact h

end InfoGeometry.Canonical.NoncommutativeGibbsTwoPointFrechetBridge
