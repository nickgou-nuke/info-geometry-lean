import InfoGeometry.Canonical.NoncommutativeGibbsTwoPointFrechetBridge
import InfoGeometry.Canonical.NoncommutativeGibbsCenteredFrechetBKMBridge
import InfoGeometry.Canonical.FiniteSelfAdjointGibbsStateBridge
import InfoGeometry.OperatorAlgebra.NoncommutativeDuhamelContinuityReduction
import InfoGeometry.OperatorAlgebra.NoncommutativeDuhamelFrechetBridge

noncomputable section
set_option autoImplicit false

namespace InfoGeometry.Canonical.NoncommutativeGibbsSecondDerivativeCenteredBridge

open SouriauOnsagerBKM
open InfoGeometry.Canonical.NoncommutativeGibbsExpectationBridge
open InfoGeometry.Canonical.NoncommutativeGibbsFaithfulNormalizationBridge
open InfoGeometry.Canonical.NoncommutativeGibbsNormalizedBKMTwoPointBridge
open InfoGeometry.Canonical.NoncommutativeGibbsTwoPointFrechetBridge
open InfoGeometry.Canonical.NoncommutativeGibbsCenteredBKMCovariance
open InfoGeometry.Canonical.FiniteSelfAdjointGibbsStateBridge
open InfoGeometry.OperatorAlgebra
open InfoGeometry.Optics.OperatorQGTFrechetChernCharacter
open InfoGeometry.Canonical.FiniteSelfAdjointGibbsStateBridge

abbrev GibbsOperator (n : ℕ) := FiniteOperatorAlgebra n

/-- The Gibbs exponential derivative is the native operator-valued Duhamel
derivative.  This is the operator-level bridge used by the two-point and
second-response constructions below. -/
theorem gibbs_exponentialDerivative_eq_duhamelDerivative
    {n : ℕ} (H : GibbsOperator n) :
    exponentialDerivative (𝕜 := ℝ) H = duhamelDerivative H := by
  apply ContinuousLinearMap.ext
  intro A
  have hcont :
      ContinuousAt
        (InfoGeometry.OperatorAlgebra.duhamelPerturbationIntegral H A) 0 := by
    simpa [InfoGeometry.OperatorAlgebra.duhamelPerturbationIntegral,
      InfoGeometry.OperatorAlgebra.duhamelDifferenceQuotient] using
      (InfoGeometry.OperatorAlgebra.continuous_duhamelDifferenceQuotient H A).continuousAt
  exact
    InfoGeometry.OperatorAlgebra.exponentialDerivative_apply_eq_duhamelDerivative_of_continuousAt
      H A hcont

theorem exponentialDerivative_complex_restrictScalars_eq_real
    {n : ℕ} (H : GibbsOperator n) :
    (exponentialDerivative (𝕜 := ℂ) H).restrictScalars ℝ =
      exponentialDerivative (𝕜 := ℝ) H := by
  exact (hasFDerivAt_exp_noncommutative
      (𝕜 := ℂ) (A := GibbsOperator n) H).restrictScalars ℝ |>.unique
      (hasFDerivAt_exp_noncommutative
      (𝕜 := ℝ) (A := GibbsOperator n) H)

theorem exponentialDerivative_complex_apply_eq_real
    {n : ℕ} (H A : GibbsOperator n) :
    exponentialDerivative (𝕜 := ℂ) H A =
      exponentialDerivative (𝕜 := ℝ) H A := by
  have h := congrArg (fun T => T A)
    (exponentialDerivative_complex_restrictScalars_eq_real H)
  exact h

noncomputable def complexNormalizedFrechetTwoPoint
    {n : ℕ} (H A B : GibbsOperator n) : ℂ :=
      finiteOperatorTrace
      (exponentialDerivative (𝕜 := ℂ) H A * B) /
    tracedExponential H

theorem complexNormalizedFrechetTwoPoint_eq_normalizedFrechetTwoPoint
    {n : ℕ} [Nonempty (Fin n)] (H A B : GibbsOperator n)
    (hH : IsSelfAdjoint H) (hZ : 0 < gibbsPartitionReal H) :
    complexNormalizedFrechetTwoPoint H A B =
      normalizedFrechetTwoPoint H A B := by
  unfold complexNormalizedFrechetTwoPoint normalizedFrechetTwoPoint
  rw [exponentialDerivative_complex_apply_eq_real H A]
  rw [tracedExponential_eq_gibbsPartitionReal H hH]
  have hZ0 : (gibbsPartitionReal H : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hZ)
  rw [div_eq_mul_inv, mul_comm]
  simp only [Complex.ofReal_inv]

/-- The exact quotient-rule second response is the centered complex
Frechet two-point response.  This is an algebraic identity, with no
commutativity assumption on the observables. -/
theorem secondResponse_eq_centered_complexResponse
    {n : ℕ} (H : GibbsOperator n) (hH : IsSelfAdjoint H)
    (hZ : 0 < gibbsPartitionReal H) (A B : GibbsOperator n) :
    ((finiteOperatorTrace
          (exponentialDerivative (𝕜 := ℂ) H A * B) *
          tracedExponential H -
        twoPointNumerator B H *
          finiteOperatorTrace (NormedSpace.exp H * A)) /
        (tracedExponential H) ^ 2) =
      complexNormalizedFrechetTwoPoint H A B -
        operatorExpectation H B * operatorExpectation H A := by
  rw [tracedExponential_eq_gibbsPartitionReal H hH]
  unfold complexNormalizedFrechetTwoPoint operatorExpectation twoPointNumerator
  simp only [normalizedExponential, smul_mul_assoc,
    finiteOperatorTrace_complex_smul, div_eq_mul_inv]
  rw [tracedExponential_eq_gibbsPartitionReal H hH]
  have hnonzero : (gibbsPartitionReal H : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hZ)
  field_simp [hnonzero]

/-- The genuine second directional derivative of the complex log-partition
gradient, with the direction `A` differentiated and the test direction `B`
held fixed. -/
noncomputable def complexDirectionalHessian
    {n : ℕ} (H A B : GibbsOperator n) : ℂ :=
  deriv (normalizedTwoPointLine H A B) 0

/-- The real restriction of the changed-origin first derivative. -/
noncomputable def realDirectionalGradientLine
    {n : ℕ} (H A B : GibbsOperator n) (t : ℝ) : ℝ :=
  (logTracedExponentialDerivative (H + (t : ℂ) • A) B).re

/--
The self-adjoint Gibbs locus supplies the slit-plane hypothesis needed by the
complex derivative theorem.  Taking the real part gives an actual real
`HasDerivAt` statement, which is the precise local interface for the real
Hessian theorem; no global real Fréchet claim is made here.
-/
theorem hasDerivAt_realDirectionalGradientLine
    {n : ℕ} [Nonempty (Fin n)]
    (H A B : GibbsOperator n) (hH : IsSelfAdjoint H) :
    HasDerivAt (realDirectionalGradientLine H A B)
      (complexDirectionalHessian H A B).re 0 := by
  unfold realDirectionalGradientLine
  change HasDerivAt _ (deriv (normalizedTwoPointLine H A B) 0).re 0
  have hEq :
      (fun z : ℂ => logTracedExponentialDerivative (H + z • A) B) =
        normalizedTwoPointLine H A B := by
    funext z
    rw [logTracedExponentialDerivative_apply_eq_expectation]
    rw [operatorExpectation_eq_trace_div]
    rfl
  rw [← hEq]
  have hC := hasDerivAt_logTracedExponentialDerivative_apply_line
    H A B (tracedExponential_mem_slitPlane_of_isSelfAdjoint H hH)
  have hderiv := hC.deriv
  rw [hderiv]
  exact hC.real_of_complex

/-- The directional Hessian is the derivative of the first log-partition
gradient evaluated on the test direction.  This is an exact derivative
statement, not merely an equality of two pre-defined response tensors. -/
theorem complexDirectionalHessian_eq_centered_complexResponse
    {n : ℕ} (H : GibbsOperator n) (hH : IsSelfAdjoint H)
    (hZ : 0 < gibbsPartitionReal H) (A B : GibbsOperator n) :
    complexDirectionalHessian H A B =
      complexNormalizedFrechetTwoPoint H A B -
        operatorExpectation H B * operatorExpectation H A := by
  unfold complexDirectionalHessian
  have htrace : tracedExponential H ≠ 0 := by
    rw [tracedExponential_eq_gibbsPartitionReal H hH]
    exact_mod_cast (ne_of_gt hZ)
  rw [deriv_normalizedTwoPointLine_at_zero H A B htrace]
  exact secondResponse_eq_centered_complexResponse H hH hZ A B

/-- The real Hessian readout is the real part of the centered noncommutative
Frechet response.  This keeps the operator ordering intact and is the
real-valued interface used by the BKM covariance bridge. -/
theorem realDirectionalHessian_eq_centeredComplexResponse_re
    {n : ℕ} (H A B : GibbsOperator n) (hH : IsSelfAdjoint H)
    (hZ : 0 < gibbsPartitionReal H) :
    (complexDirectionalHessian H A B).re =
      (complexNormalizedFrechetTwoPoint H A B).re -
        (operatorExpectation H B * operatorExpectation H A).re := by
  rw [complexDirectionalHessian_eq_centered_complexResponse H hH hZ A B]
  simp only [Complex.sub_re]

theorem complexDirectionalHessian_of_commuting_direction
    {n : ℕ} (H A B : GibbsOperator n)
    (hSlit : tracedExponential H ∈ Complex.slitPlane)
    (hComm : Commute H A) :
    complexDirectionalHessian H A B =
    ((finiteOperatorTrace (NormedSpace.exp H * A * B) *
          tracedExponential H -
        finiteOperatorTrace (NormedSpace.exp H * B) *
          finiteOperatorTrace (NormedSpace.exp H * A)) /
        (tracedExponential H) ^ 2) := by
  unfold complexDirectionalHessian
  have hEq :
      (fun z : ℂ => logTracedExponentialDerivative (H + z • A) B) =
        normalizedTwoPointLine H A B := by
    funext z
    rw [logTracedExponentialDerivative_apply_eq_expectation]
    rw [operatorExpectation_eq_trace_div]
    rfl
  rw [← hEq]
  exact (hasDerivAt_logTracedExponentialDerivative_apply_line_of_commute
    H A B hSlit hComm).deriv

theorem complexDirectionalHessian_of_selfAdjoint_commuting_direction
    {n : ℕ} [Nonempty (Fin n)] (H A B : GibbsOperator n)
    (hH : IsSelfAdjoint H) (hComm : Commute H A) :
    complexDirectionalHessian H A B =
      ((finiteOperatorTrace (NormedSpace.exp H * A * B) *
          tracedExponential H -
        finiteOperatorTrace (NormedSpace.exp H * B) *
          finiteOperatorTrace (NormedSpace.exp H * A)) /
        (tracedExponential H) ^ 2) := by
  exact complexDirectionalHessian_of_commuting_direction H A B
    (tracedExponential_mem_slitPlane_of_isSelfAdjoint H hH) hComm

theorem complexNormalizedFrechetTwoPoint_re_eq_normalizedFrechetTwoPoint_re_of_commute
    {n : ℕ} [Nonempty (Fin n)] (H A B : GibbsOperator n)
    (hH : IsSelfAdjoint H) (hComm : Commute H A) :
    (complexNormalizedFrechetTwoPoint H A B).re =
      (normalizedFrechetTwoPoint H A B).re := by
  unfold complexNormalizedFrechetTwoPoint normalizedFrechetTwoPoint
  rw [exponentialDerivative_apply_of_commute_complex H A hComm.symm]
  rw [exponentialDerivative_apply_of_commute H A hComm.symm]
  rw [tracedExponential_eq_gibbsPartitionReal H hH]
  have hZ : 0 < gibbsPartitionReal H := by
    simpa [gibbsPartitionReal] using
      (tracedExponential_re_pos_of_isSelfAdjoint H hH)
  simp only [Complex.div_re, Complex.ofReal_re, Complex.ofReal_im]
  simp [Complex.normSq]
  field_simp [ne_of_gt hZ]

theorem expectationReal_faithfulGibbsDensity_eq_operatorExpectation_re
    {n : ℕ} [Nonempty (Fin n)] (H B : GibbsOperator n)
    (hH : IsSelfAdjoint H) :
    expectationReal (faithfulGibbsDensity H hH
      (by
        simpa [gibbsPartitionReal] using
          (tracedExponential_re_pos_of_isSelfAdjoint H hH))) B =
      (operatorExpectation H B).re := by
  unfold expectationReal
  rw [operatorExpectation_eq_faithfulGibbsTrace H B hH]
  rfl

theorem operatorExpectation_im_eq_zero_of_isSelfAdjoint
    {n : ℕ} [Nonempty (Fin n)] (H B : GibbsOperator n)
    (hH : IsSelfAdjoint H) (hB : IsSelfAdjoint B) :
    (operatorExpectation H B).im = 0 := by
  rw [operatorExpectation_eq_faithfulGibbsTrace H B hH]
  have hstar :
      star (finiteOperatorTrace
        ((faithfulGibbsDensityOperator H hH).rho * B)) =
        finiteOperatorTrace ((faithfulGibbsDensityOperator H hH).rho * B) := by
    calc
      star (finiteOperatorTrace
          ((faithfulGibbsDensityOperator H hH).rho * B)) =
          finiteOperatorTrace (star
            ((faithfulGibbsDensityOperator H hH).rho * B)) :=
        (finiteOperatorTrace_star _).symm
      _ = finiteOperatorTrace
          (star B * star (faithfulGibbsDensityOperator H hH).rho) := by
        rw [star_mul]
      _ = finiteOperatorTrace
          (B * (faithfulGibbsDensityOperator H hH).rho) := by
        rw [hB.star_eq,
          (faithfulGibbsDensityOperator H hH).strictlyPositive.isSelfAdjoint.star_eq]
      _ = finiteOperatorTrace
          ((faithfulGibbsDensityOperator H hH).rho * B) :=
        finiteOperatorTrace_mul_comm _ _
  have him := congrArg Complex.im hstar
  simp only [Complex.star_def, Complex.conj_im] at him
  linarith

theorem realDirectionalHessian_eq_centeredBKMRealCovariance
    {n : ℕ} [Nonempty (Fin n)] (H A B : GibbsOperator n)
    (hH : IsSelfAdjoint H) (hZ : 0 < gibbsPartitionReal H)
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) :
    (complexDirectionalHessian H A B).re =
      centeredBKMRealCovariance
        (faithfulGibbsDensity H hH hZ)
        (continuous_faithfulGibbsDensity_rpow H hH hZ) A B := by
  rw [complexDirectionalHessian_eq_centered_complexResponse H hH hZ A B]
  rw [complexNormalizedFrechetTwoPoint_eq_normalizedFrechetTwoPoint
    H A B hH hZ]
  rw [normalizedFrechetTwoPoint_eq_kuboMoriPairing H hH hZ A B,
    hA.star_eq]
  rw [centeredBKMRealCovariance_eq]
  have hA_im := operatorExpectation_im_eq_zero_of_isSelfAdjoint H A hH hA
  have hB_im := operatorExpectation_im_eq_zero_of_isSelfAdjoint H B hH hB
  have hA_re := expectationReal_faithfulGibbsDensity_eq_operatorExpectation_re
    H A hH
  have hB_re := expectationReal_faithfulGibbsDensity_eq_operatorExpectation_re
    H B hH
  simp only [Complex.sub_re, Complex.mul_re, hA_im, hB_im, zero_mul,
    sub_zero, hA_re, hB_re]
  rw [FaithfulDensityOperator.bkmRealBilinForm_apply]
  ring

end InfoGeometry.Canonical.NoncommutativeGibbsSecondDerivativeCenteredBridge
