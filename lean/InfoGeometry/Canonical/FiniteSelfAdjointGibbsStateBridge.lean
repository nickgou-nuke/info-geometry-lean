import Mathlib.Analysis.Complex.RealDeriv
import InfoGeometry.Canonical.NoncommutativeGibbsExpectationCyclicDerivative
import InfoGeometry.Canonical.NoncommutativeGibbsFaithfulNormalizationBridge
import InfoGeometry.Canonical.SouriauOnsagerBKMPositivity

/-!
# Finite self-adjoint Gibbs state bridge

The arbitrary-direction Gibbs expectation theorem uses the principal complex
logarithm and therefore carries an explicit slit-plane premise.  On the
self-adjoint finite-operator locus that premise is not additional data:
`exp H` factors as a positive square, its finite trace is a strictly positive
real number, and normalization produces the repository-native
`FaithfulDensityOperator`.

No diagonalisation, spectral witness, supplied positivity law, or parallel
density carrier is introduced.
-/

noncomputable section
set_option autoImplicit false

namespace InfoGeometry.Canonical.FiniteSelfAdjointGibbsStateBridge

open Complex
open SouriauOnsagerBKM
open InfoGeometry.Canonical.NoncommutativeGibbsExpectationBridge
open InfoGeometry.Canonical.NoncommutativeGibbsFaithfulNormalizationBridge

abbrev Operator (n : ℕ) := FiniteOperatorAlgebra n

/-- A self-adjoint exponential is the positive square
`exp(H/2)⋆ exp(H/2)`. -/
theorem exp_eq_star_exp_half_mul_exp_half
    {n : ℕ} (H : Operator n) (hH : IsSelfAdjoint H) :
    NormedSpace.exp H =
      star (NormedSpace.exp ((1 / 2 : ℂ) • H)) *
        NormedSpace.exp ((1 / 2 : ℂ) • H) := by
  have hhalf_sum :
      ((1 / 2 : ℂ) • H) + ((1 / 2 : ℂ) • H) = H := by
    rw [← two_smul ℂ, smul_smul]
    rw [show (2 : ℂ) * (1 / 2 : ℂ) = 1 by norm_num, one_smul]
  letI : NormedAlgebra ℚ (Operator n) :=
    NormedAlgebra.restrictScalars ℚ ℂ (Operator n)
  letI : StarModule ℝ (Operator n) := ⟨by
    intro r x
    change star ((r : ℂ) • x) = r • star x
    rw [star_smul]
    simpa [Complex.star_def] using
      (real_smul_eq_complex_smul r (star x)).symm⟩
  symm
  have hhalf :
      star ((1 / 2 : ℂ) • H) = (1 / 2 : ℂ) • H := by
    rw [star_smul, hH.star_eq]
    norm_num
  calc
    star (NormedSpace.exp ((1 / 2 : ℂ) • H)) *
          NormedSpace.exp ((1 / 2 : ℂ) • H) =
        NormedSpace.exp (star ((1 / 2 : ℂ) • H)) *
          NormedSpace.exp ((1 / 2 : ℂ) • H) := by
            rw [NormedSpace.star_exp]
    _ = NormedSpace.exp ((1 / 2 : ℂ) • H) *
          NormedSpace.exp ((1 / 2 : ℂ) • H) := by
            rw [hhalf]
    _ = NormedSpace.exp
          (((1 / 2 : ℂ) • H) + ((1 / 2 : ℂ) • H)) := by
            rw [NormedSpace.exp_add_of_commute (Commute.refl _)]
    _ = NormedSpace.exp H := by
      rw [hhalf_sum]

/-- The exponential of a self-adjoint finite operator is nonnegative. -/
theorem exp_nonneg_of_isSelfAdjoint
    {n : ℕ} (H : Operator n) (hH : IsSelfAdjoint H) :
    0 ≤ NormedSpace.exp H := by
  exact hH.exp_nonneg
/-- The exponential of a self-adjoint finite operator is strictly positive. -/
theorem exp_isStrictlyPositive_of_isSelfAdjoint
    {n : ℕ} (H : Operator n) (hH : IsSelfAdjoint H) :
    IsStrictlyPositive (NormedSpace.exp H) := by
  exact exp_isStrictlyPositive H hH
/-- The traced exponential is fixed by complex conjugation. -/
theorem star_tracedExponential_of_isSelfAdjoint
    {n : ℕ} (H : Operator n) (hH : IsSelfAdjoint H) :
    star (tracedExponential H) = tracedExponential H := by
  letI : NormedAlgebra ℚ (Operator n) :=
    NormedAlgebra.restrictScalars ℚ ℂ (Operator n)
  unfold tracedExponential
  rw [← finiteOperatorTrace_star]
  rw [NormedSpace.star_exp, hH.star_eq]

/-- The traced exponential of a self-adjoint generator is real. -/
theorem tracedExponential_im_eq_zero_of_isSelfAdjoint
    {n : ℕ} (H : Operator n) (hH : IsSelfAdjoint H) :
    (tracedExponential H).im = 0 := by
  have hstar := star_tracedExponential_of_isSelfAdjoint H hH
  have him := congrArg Complex.im hstar
  simp only [star_def, conj_im] at him
  linarith

/-- The traced exponential equals the complex embedding of its real part. -/
theorem tracedExponential_eq_ofReal_re_of_isSelfAdjoint
    {n : ℕ} (H : Operator n) (hH : IsSelfAdjoint H) :
    tracedExponential H = ((tracedExponential H).re : ℂ) := by
  apply Complex.ext
  · simp
  · simpa using tracedExponential_im_eq_zero_of_isSelfAdjoint H hH

/-- In nonzero finite dimension, the trace of a self-adjoint exponential is
strictly positive. -/
theorem tracedExponential_re_pos_of_isSelfAdjoint
    {n : ℕ} [Nonempty (Fin n)]
    (H : Operator n) (hH : IsSelfAdjoint H) :
    0 < (tracedExponential H).re := by
  letI : NormedAlgebra ℚ (Operator n) :=
    NormedAlgebra.restrictScalars ℚ ℂ (Operator n)
  rw [tracedExponential,
    exp_eq_star_exp_half_mul_exp_half H hH]
  exact finiteOperatorTrace_star_mul_self_re_pos _
    (NormedSpace.isUnit_exp ((1 / 2 : ℂ) • H)).ne_zero

/-- The principal-log branch condition is automatic for a self-adjoint finite
operator in nonzero dimension. -/
theorem tracedExponential_mem_slitPlane_of_isSelfAdjoint
    {n : ℕ} [Nonempty (Fin n)]
    (H : Operator n) (hH : IsSelfAdjoint H) :
    tracedExponential H ∈ Complex.slitPlane := by
  rw [tracedExponential_eq_ofReal_re_of_isSelfAdjoint H hH]
  exact Complex.ofReal_mem_slitPlane.2
    (tracedExponential_re_pos_of_isSelfAdjoint H hH)

/-- Real scalar multiplication pulled through the finite operator trace. -/
theorem finiteOperatorTrace_real_smul
    {n : ℕ} (r : ℝ) (A : Operator n) :
    finiteOperatorTrace (r • A) =
      (r : ℂ) * finiteOperatorTrace A := by
  change finiteOperatorTrace ((r : ℂ) • A) =
    (r : ℂ) * finiteOperatorTrace A
  exact finiteOperatorTrace_complex_smul (r : ℂ) A

/-- Normalized positive exponential weight. -/
noncomputable def faithfulNormalizedExponential
    {n : ℕ} (H : Operator n) : Operator n :=
  ((tracedExponential H).re)⁻¹ • NormedSpace.exp H

/-- The normalized exponential remains strictly positive. -/
theorem faithfulNormalizedExponential_isStrictlyPositive
    {n : ℕ} [Nonempty (Fin n)]
    (H : Operator n) (hH : IsSelfAdjoint H) :
    IsStrictlyPositive (faithfulNormalizedExponential H) := by
  unfold faithfulNormalizedExponential
  letI : Algebra ℝ (Operator n) := Algebra.ofModule (by
    intro r x y
    change ((r : ℂ) • x) * y = (r : ℂ) • (x * y)
    exact smul_mul_assoc (r : ℂ) x y) (by
    intro r x y
    change x * ((r : ℂ) • y) = (r : ℂ) • (x * y)
    exact mul_smul_comm (r : ℂ) x y)
  exact IsStrictlyPositive.smul
    (inv_pos.mpr (tracedExponential_re_pos_of_isSelfAdjoint H hH))
    (exp_isStrictlyPositive_of_isSelfAdjoint H hH)

/-- The normalized exponential has finite trace one. -/
theorem finiteOperatorTrace_faithfulNormalizedExponential
    {n : ℕ} [Nonempty (Fin n)]
    (H : Operator n) (hH : IsSelfAdjoint H) :
    finiteOperatorTrace (faithfulNormalizedExponential H) = 1 := by
  have hpos := tracedExponential_re_pos_of_isSelfAdjoint H hH
  have hreal := tracedExponential_eq_ofReal_re_of_isSelfAdjoint H hH
  unfold faithfulNormalizedExponential
  rw [finiteOperatorTrace_real_smul]
  change ((((tracedExponential H).re)⁻¹ : ℝ) : ℂ) *
      tracedExponential H = 1
  rw [hreal]
  norm_cast
  exact inv_mul_cancel₀ hpos.ne'

/-- The genuine normalized Gibbs weight as the repository-native faithful
finite density operator. -/
noncomputable def faithfulGibbsDensityOperator
    {n : ℕ} [Nonempty (Fin n)]
    (H : Operator n) (hH : IsSelfAdjoint H) :
    FaithfulDensityOperator n where
  rho := faithfulNormalizedExponential H
  strictlyPositive :=
    faithfulNormalizedExponential_isStrictlyPositive H hH
  trace_one :=
    finiteOperatorTrace_faithfulNormalizedExponential H hH

/-- The normalization used by the expectation owner is exactly the faithful
Gibbs density on the self-adjoint locus. -/
theorem normalizedExponential_eq_faithfulGibbsDensity
    {n : ℕ} [Nonempty (Fin n)]
    (H : Operator n) (hH : IsSelfAdjoint H) :
    normalizedExponential H =
      (faithfulGibbsDensityOperator H hH).rho := by
  dsimp [normalizedExponential, faithfulGibbsDensityOperator,
    faithfulNormalizedExponential]
  rw [tracedExponential_eq_ofReal_re_of_isSelfAdjoint H hH]
  rw [← Complex.ofReal_inv]
  rw [real_smul_eq_complex_smul]
  congr 1

/-- Operator expectation is the finite trace pairing against the native
faithful Gibbs density. -/
theorem operatorExpectation_eq_faithfulGibbsTrace
    {n : ℕ} [Nonempty (Fin n)]
    (H T : Operator n) (hH : IsSelfAdjoint H) :
    operatorExpectation H T =
      finiteOperatorTrace
        ((faithfulGibbsDensityOperator H hH).rho * T) := by
  unfold operatorExpectation
  rw [normalizedExponential_eq_faithfulGibbsDensity H hH]

/-- Full noncommutative expectation theorem on the self-adjoint Gibbs locus;
the principal-log branch premise is discharged internally. -/
theorem hasDerivAt_logPartitionLine_eq_expectation_of_isSelfAdjoint
    {n : ℕ} [Nonempty (Fin n)]
    (H T : Operator n) (hH : IsSelfAdjoint H) :
    HasDerivAt (logPartitionLine H T)
      (operatorExpectation H T) 0 :=
  hasDerivAt_logPartitionLine_eq_expectation H T
    (tracedExponential_mem_slitPlane_of_isSelfAdjoint H hH)

/-- Real readout of the principal log-partition line. -/
noncomputable def realLogPartitionLine
    {n : ℕ} (H T : Operator n) (t : ℝ) : ℝ :=
  (logPartitionLine H T (t : ℂ)).re

/-- Real readout of the normalized operator expectation. -/
noncomputable def realOperatorExpectation
    {n : ℕ} (H T : Operator n) : ℝ :=
  (operatorExpectation H T).re

/-- The real thermodynamic chart inherits the full noncommutative expectation
derivative from the complex analytic theorem. -/
theorem hasDerivAt_realLogPartitionLine_eq_expectation
    {n : ℕ} [Nonempty (Fin n)]
    (H T : Operator n) (hH : IsSelfAdjoint H) :
    HasDerivAt (realLogPartitionLine H T)
      (realOperatorExpectation H T) 0 := by
  simpa [realLogPartitionLine, realOperatorExpectation] using
    (hasDerivAt_logPartitionLine_eq_expectation_of_isSelfAdjoint
      H T hH).real_of_complex

end InfoGeometry.Canonical.FiniteSelfAdjointGibbsStateBridge
