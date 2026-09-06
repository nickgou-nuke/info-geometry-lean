import InfoGeometry.Canonical.NoncommutativeGibbsCenteredFrechetBKMBridge
import InfoGeometry.Thermo.SouriauOnsagerBKMOperatorForms

/-!
# Additive Gibbs Hessian and centered BKM covariance

This owner packages the actual second variation of the additive Gibbs
log-partition.  It differentiates the already proved Fréchet differential
field along the affine line `H + z • A`; it does not use the conjugation-orbit
`deriv2` from `OperatorialHessianBridge`.
-/

noncomputable section
set_option autoImplicit false

namespace InfoGeometry.Canonical.NoncommutativeGibbsBKMHessianBridge

open SouriauOnsagerBKM
open InfoGeometry.OperatorAlgebra
open InfoGeometry.OperatorAlgebra.ExteriorAlgebra
open InfoGeometry.OperatorAlgebra.NoncommutativePowerDerivative
open InfoGeometry.Canonical.NoncommutativeGibbsExpectationBridge
open InfoGeometry.Canonical.NoncommutativeGibbsTwoPointFrechetBridge
open InfoGeometry.Canonical.NoncommutativeGibbsFaithfulNormalizationBridge
open InfoGeometry.Canonical.NoncommutativeGibbsNormalizedBKMTwoPointBridge
open InfoGeometry.Canonical.NoncommutativeGibbsCenteredBKMCovariance
open InfoGeometry.Canonical.NoncommutativeGibbsCenteredFrechetBKMBridge

abbrev Operator (n : ℕ) := FiniteOperatorAlgebra n

/-- The first Fréchet differential of the log-partition, evaluated at `B`,
along the additive affine line `H + z • A`. -/
noncomputable def logPartitionGradientLine
    {n : ℕ} (H A B : Operator n) (z : ℂ) : ℂ :=
  normalizedTwoPointLine H A B z

/-- The gradient-line definition is the evaluation of the genuine first
Fréchet differential field of `logTracedExponential`. -/
theorem logPartitionGradientLine_eq_logTracedExponentialDerivative
    {n : ℕ} (H A B : Operator n) (z : ℂ) :
    logPartitionGradientLine H A B z =
      logTracedExponentialDerivative (H + z • A) B := by
  unfold logPartitionGradientLine normalizedTwoPointLine
  rw [logTracedExponentialDerivative_apply_eq_expectation]
  rw [operatorExpectation_eq_trace_div]
  rfl

/-- Complex mixed response obtained by differentiating the normalized first
moment.  This is the unprojected complex Hessian readout. -/
noncomputable def complexGibbsHessianResponse
    {n : ℕ} (H A B : Operator n) : ℂ :=
  (tracedExponential H)⁻¹ *
      finiteOperatorTrace
        (exponentialDerivative (𝕜 := ℂ) H A * B) -
    operatorExpectation H A * operatorExpectation H B

/-- Quotient-rule differentiation of the genuine first Fréchet differential
field.  No commutativity assumption is used. -/
theorem hasDerivAt_logPartitionGradientLine
    {n : ℕ} (H A B : Operator n)
    (hZ : tracedExponential H ≠ 0) :
    HasDerivAt (logPartitionGradientLine H A B)
      (complexGibbsHessianResponse H A B) 0 := by
  unfold logPartitionGradientLine
  have h := hasDerivAt_normalizedTwoPointLine H A B hZ
  convert h using 1
  unfold complexGibbsHessianResponse
  rw [operatorExpectation_eq_trace_div H A]
  rw [operatorExpectation_eq_trace_div H B]
  unfold twoPointNumerator
  field_simp [hZ]
  ring

/-- Actual mixed second derivative readout of the additive Gibbs
log-partition: the derivative of its proved first Fréchet differential field. -/
noncomputable def secondFDerivLogPartitionReadout
    {n : ℕ} (H A B : Operator n) : ℂ :=
  deriv (logPartitionGradientLine H A B) 0

theorem secondFDerivLogPartitionReadout_eq_complexResponse
    {n : ℕ} (H A B : Operator n)
    (hZ : tracedExponential H ≠ 0) :
    secondFDerivLogPartitionReadout H A B =
      complexGibbsHessianResponse H A B := by
  exact (hasDerivAt_logPartitionGradientLine H A B hZ).deriv

/-- The repository expectation agrees with the readout in the native faithful
Gibbs density. -/
theorem operatorExpectation_eq_faithfulGibbsDensity_expectation
    {n : ℕ} (H : Operator n) (hH : IsSelfAdjoint H)
    (hZ : 0 < gibbsPartitionReal H) (A : Operator n) :
    operatorExpectation H A =
      finiteOperatorTrace ((faithfulGibbsDensity H hH hZ).rho * A) := by
  unfold operatorExpectation
  rw [faithfulGibbsDensity_rho_eq_normalizedExponential H hH hZ]

/-- A self-adjoint observable has a real Gibbs expectation. -/
theorem operatorExpectation_im_eq_zero_of_isSelfAdjoint
    {n : ℕ} (H : Operator n) (hH : IsSelfAdjoint H)
    (hZ : 0 < gibbsPartitionReal H)
    (A : Operator n) (hA : IsSelfAdjoint A) :
    (operatorExpectation H A).im = 0 := by
  rw [operatorExpectation_eq_faithfulGibbsDensity_expectation H hH hZ A]
  let D := faithfulGibbsDensity H hH hZ
  have hstar :
      star (finiteOperatorTrace (D.rho * A)) =
        finiteOperatorTrace (D.rho * A) := by
    calc
      star (finiteOperatorTrace (D.rho * A)) =
          finiteOperatorTrace (star (D.rho * A)) :=
        (finiteOperatorTrace_star (D.rho * A)).symm
      _ = finiteOperatorTrace (star A * star D.rho) := by rw [star_mul]
      _ = finiteOperatorTrace (A * D.rho) := by
        rw [hA.star_eq, D.strictlyPositive.isSelfAdjoint.star_eq]
      _ = finiteOperatorTrace (D.rho * A) :=
        finiteOperatorTrace_mul_comm A D.rho
  have him := congrArg Complex.im hstar
  simp only [star_def, Complex.conj_im] at him
  linarith

/-- In the faithful self-adjoint specialization, the real part of the actual
complex Hessian response is exactly the centered Fréchet response. -/
theorem complexGibbsHessianResponse_re_eq_centeredFrechetResponse
    {n : ℕ} (H : Operator n) (hH : IsSelfAdjoint H)
    (hZ : 0 < gibbsPartitionReal H)
    (A B : Operator n) (hA : IsSelfAdjoint A) :
    (complexGibbsHessianResponse H A B).re =
      centeredFrechetResponse H hH hZ A B := by
  unfold complexGibbsHessianResponse centeredFrechetResponse
  rw [tracedExponential_eq_gibbsPartitionReal H hH]
  rw [operatorExpectation_eq_faithfulGibbsDensity_expectation H hH hZ A]
  rw [operatorExpectation_eq_faithfulGibbsDensity_expectation H hH hZ B]
  rw [Complex.sub_re, Complex.mul_re]
  have hAim :
      (finiteOperatorTrace
        ((faithfulGibbsDensity H hH hZ).rho * A)).im = 0 := by
    rw [← operatorExpectation_eq_faithfulGibbsDensity_expectation H hH hZ A]
    exact operatorExpectation_im_eq_zero_of_isSelfAdjoint H hH hZ A hA
  simp [normalizedFrechetTwoPoint, expectationReal, Complex.mul_re, hAim]

/-- Capstone: the real mixed second Fréchet derivative of the additive Gibbs
log-partition is the native centered BKM covariance. -/
theorem secondFDeriv_logPartition_apply_eq_centeredBKM
    {n : ℕ} (H : Operator n) (hH : IsSelfAdjoint H)
    (hZ : 0 < gibbsPartitionReal H)
    (A B : Operator n) (hA : IsSelfAdjoint A) :
    (secondFDerivLogPartitionReadout H A B).re =
      centeredBKMRealCovariance
        (faithfulGibbsDensity H hH hZ)
        (continuous_faithfulGibbsDensity_rpow H hH hZ)
        A B := by
  have hZc : tracedExponential H ≠ 0 := by
    rw [tracedExponential_eq_gibbsPartitionReal H hH]
    exact_mod_cast hZ.ne'
  rw [secondFDerivLogPartitionReadout_eq_complexResponse H A B hZc]
  rw [complexGibbsHessianResponse_re_eq_centeredFrechetResponse
    H hH hZ A B hA]
  exact centeredFrechetResponse_eq_centeredBKMRealCovariance
    H hH hZ A B hA

/-! ## Reconciliation with the operator-form and Onsager layers -/

/-- Genuine two-vector pullback of the BKM bilinear form.  Unlike
`bkmOperator1Form`, the two tangent vectors are not forced to coincide. -/
noncomputable def bkmOperatorBilinForm
    {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℝ V]
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (α β : Op1Form ℝ V (Operator n)) (u v : V) : ℝ :=
  D.bkmRealBilinForm hpow (α u) (β v)

/-- The historical one-vector readout is the diagonal restriction of the
two-vector pullback. -/
theorem bkmOperatorBilinForm_diag_eq_bkmOperator1Form
    {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℝ V]
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (α β : Op1Form ℝ V (Operator n)) (u : V) :
    bkmOperatorBilinForm D hpow α β u u =
      InfoGeometry.Thermo.SouriauOnsagerBKMOperatorForms.bkmOperator1Form
        D hpow α β u :=
  rfl

/-- Centered two-vector pullback appropriate to an additive Gibbs Hessian. -/
noncomputable def centeredBKMOperatorBilinForm
    {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℝ V]
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (α β : Op1Form ℝ V (Operator n)) (u v : V) : ℝ :=
  centeredBKMRealCovariance D hpow (α u) (β v)

/-- Pullback form of the capstone theorem for two independent tangent
vectors. -/
theorem secondFDeriv_logPartition_pullback_eq_centeredBKMOperatorBilinForm
    {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℝ V]
    (H : Operator n) (hH : IsSelfAdjoint H)
    (hZ : 0 < gibbsPartitionReal H)
    (α β : Op1Form ℝ V (Operator n)) (u v : V)
    (hα : IsSelfAdjoint (α u)) :
    (secondFDerivLogPartitionReadout H (α u) (β v)).re =
      centeredBKMOperatorBilinForm
        (faithfulGibbsDensity H hH hZ)
        (continuous_faithfulGibbsDensity_rpow H hH hZ)
        α β u v := by
  unfold centeredBKMOperatorBilinForm
  exact secondFDeriv_logPartition_apply_eq_centeredBKM
    H hH hZ (α u) (β v) hα

/-- Canonical positive Onsager form carried by a faithful density. -/
noncomputable def faithfulDensityBKMOnsagerForm
    {n : ℕ} (D : FaithfulDensityOperator n)
    (hpow : Continuous D.rpow) :
    InfoGeometry.Thermo.SusceptibilityOnsagerStress.OnsagerTwoOperatorForm
      (Operator n) :=
  D.bkmOnsagerForm hpow
    (fun A => D.kuboMoriPairing_self_re_nonneg A hpow)

/-- The additive Gibbs Hessian is the associated Onsager form evaluated on
centered sufficient statistics. -/
theorem secondFDeriv_logPartition_eq_bkmOnsagerForm_centered
    {n : ℕ} (H : Operator n) (hH : IsSelfAdjoint H)
    (hZ : 0 < gibbsPartitionReal H)
    (A B : Operator n) (hA : IsSelfAdjoint A) :
    (secondFDerivLogPartitionReadout H A B).re =
      (faithfulDensityBKMOnsagerForm
        (faithfulGibbsDensity H hH hZ)
        (continuous_faithfulGibbsDensity_rpow H hH hZ)).form
          (centeredStatistic (faithfulGibbsDensity H hH hZ) A)
          (centeredStatistic (faithfulGibbsDensity H hH hZ) B) := by
  rw [secondFDeriv_logPartition_apply_eq_centeredBKM H hH hZ A B hA]
  rfl

end InfoGeometry.Canonical.NoncommutativeGibbsBKMHessianBridge
