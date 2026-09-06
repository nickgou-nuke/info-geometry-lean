import InfoGeometry.Canonical.NoncommutativeGibbsExpectationCyclicDerivative

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
open InfoGeometry.OperatorAlgebra.NoncommutativePowerDerivative
open InfoGeometry.Canonical.NoncommutativeGibbsExpectationBridge

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
  simpa using
    (hasFDerivAt_twoPointNumerator H B).comp_hasDerivAt_of_eq
      (0 : ℂ) hLine (by simp)

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
  unfold normalizedTwoPointLine
  convert hNum.div hDen (by simpa [partitionLine] using hZ) using 1 <;>
    simp [partitionLine, twoPointNumerator]

end InfoGeometry.Canonical.NoncommutativeGibbsTwoPointFrechetBridge
