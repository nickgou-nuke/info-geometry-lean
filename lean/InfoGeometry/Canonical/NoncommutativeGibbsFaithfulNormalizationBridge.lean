import InfoGeometry.Canonical.NoncommutativeGibbsDuhamelTwoPointBridge
import InfoGeometry.Canonical.NoncommutativeGibbsRpowNormalizationBridge
import Mathlib.Tactic

/-!
# Faithful Gibbs normalization on the finite operator carrier

This owner turns a self-adjoint finite exponential into the repository-native
`FaithfulDensityOperator`.  It then closes the syntactic transport left open
by `normalizedGibbsCFC_rpow`:

`rho^s = Z^(-s) • exp(s • H)`.

No eigenbasis, diagonalization, logarithmic branch, alternate density carrier,
or Hessian claim is introduced.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace InfoGeometry.Canonical.NoncommutativeGibbsFaithfulNormalizationBridge

open SouriauOnsagerBKM
open SouriauOnsagerBKM.FaithfulDensityOperator
open InfoGeometry.OperatorAlgebra
open InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.CblinfunMatrix
open InfoGeometry.Canonical.NoncommutativeGibbsExpectationBridge
open InfoGeometry.Canonical.NoncommutativeGibbsRpowNormalizationBridge

abbrev Operator (n : ℕ) := FiniteOperatorAlgebra n

/- The real structure is restriction of the existing complex scalar action. -/
noncomputable instance realOperatorModule (n : ℕ) : Module ℝ (Operator n) :=
  Module.compHom (Operator n) Complex.ofRealHom

noncomputable instance realOperatorNormedSpace (n : ℕ) :
    NormedSpace ℝ (Operator n) :=
  NormedSpace.restrictScalars ℝ ℂ (Operator n)

theorem real_smul_eq_complex_smul
    {n : ℕ} (r : ℝ) (X : Operator n) :
    r • X = (r : ℂ) • X := by
  apply matrixOfOp_injective
  rw [matrixOfOp_real_smul, matrixOfOp_complex_smul]

/-- Real partition readout for a finite operator exponential. -/
noncomputable def gibbsPartitionReal {n : ℕ} (H : Operator n) : ℝ :=
  (tracedExponential H).re

/-- The trace of a self-adjoint finite operator is real. -/
theorem finiteOperatorTrace_eq_real_of_isSelfAdjoint
    {n : ℕ} (X : Operator n) (hX : IsSelfAdjoint X) :
    finiteOperatorTrace X = (finiteOperatorTrace X).re := by
  have hstar :
      star (finiteOperatorTrace X) = finiteOperatorTrace X := by
    calc
      star (finiteOperatorTrace X) =
          finiteOperatorTrace (star X) :=
        (finiteOperatorTrace_star X).symm
      _ = finiteOperatorTrace X := by rw [hX.star_eq]
  apply Complex.ext
  · simp
  · have him := congrArg Complex.im hstar
    simp only [Complex.star_def, Complex.conj_im] at him
    simp
    linarith

/-- For a self-adjoint exponent, the complex trace is its real partition. -/
theorem tracedExponential_eq_gibbsPartitionReal
    {n : ℕ} (H : Operator n) (hH : IsSelfAdjoint H) :
    tracedExponential H = gibbsPartitionReal H := by
  unfold tracedExponential gibbsPartitionReal
  exact finiteOperatorTrace_eq_real_of_isSelfAdjoint
    (NormedSpace.exp H) hH.exp

/-- The Banach exponential of a self-adjoint element is strictly positive. -/
theorem exp_isStrictlyPositive
    {n : ℕ} (H : Operator n) (hH : IsSelfAdjoint H) :
    IsStrictlyPositive (NormedSpace.exp H) :=
  letI : NormedAlgebra ℚ (Operator n) :=
    NormedAlgebra.restrictScalars ℚ ℂ (Operator n)
  ⟨hH.exp_nonneg, NormedSpace.isUnit_exp H⟩

/-- The normalized exponential as the native faithful density operator. -/
noncomputable def faithfulGibbsDensity
    {n : ℕ} (H : Operator n) (hH : IsSelfAdjoint H)
    (hZ : 0 < gibbsPartitionReal H) :
    FaithfulDensityOperator n := by
  letI : Algebra ℝ (Operator n) := Algebra.ofModule (by
    intro r x y
    change ((r : ℂ) • x) * y = (r : ℂ) • (x * y)
    exact smul_mul_assoc (r : ℂ) x y) (by
    intro r x y
    change x * ((r : ℂ) • y) = (r : ℂ) • (x * y)
    exact mul_smul_comm (r : ℂ) x y)
  let rho : Operator n := (gibbsPartitionReal H)⁻¹ • NormedSpace.exp H
  refine { rho := rho, strictlyPositive := ?_, trace_one := ?_ }
  · exact IsStrictlyPositive.smul (inv_pos.mpr hZ)
      (exp_isStrictlyPositive H hH)
  ·
    change finiteOperatorTrace rho = 1
    dsimp [rho]
    rw [real_smul_eq_complex_smul]
    rw [finiteOperatorTrace_complex_smul]
    norm_num
    have htrace : finiteOperatorTrace (NormedSpace.exp H) =
        gibbsPartitionReal H := by
      simpa [gibbsPartitionReal] using
        (finiteOperatorTrace_eq_real_of_isSelfAdjoint
          (NormedSpace.exp H) hH.exp)
    rw [htrace]
    field_simp [ne_of_gt hZ]

/-- The faithful density is the existing normalized exponential. -/
theorem faithfulGibbsDensity_rho_eq_normalizedExponential
    {n : ℕ} (H : Operator n) (hH : IsSelfAdjoint H)
    (hZ : 0 < gibbsPartitionReal H) :
    (faithfulGibbsDensity H hH hZ).rho =
      normalizedExponential H := by
  dsimp [faithfulGibbsDensity, normalizedExponential]
  rw [tracedExponential_eq_gibbsPartitionReal H hH]
  rw [real_smul_eq_complex_smul]
  congr 1
  norm_num

/-- Final CFC-to-Banach transport for the normalized Gibbs power law. -/
theorem normalizedGibbsCFC_rpow_eq_smul_exp
    {n : ℕ} (H : Operator n) (hH : IsSelfAdjoint H)
    (Z s : ℝ) (hZ : 0 < Z) :
    CFC.rpow (cfc (normalizedScalarGibbsWeight Z) H) s =
      Z ^ (-s) • NormedSpace.exp (s • H) := by
  letI : NormedSpace ℝ (Operator n) :=
    NormedSpace.restrictScalars ℝ ℂ (Operator n)
  letI : NormedAlgebra ℝ (Operator n) :=
    NormedAlgebra.restrictScalars ℝ ℂ (Operator n)
  letI : NormedAlgebra ℚ (Operator n) :=
    NormedAlgebra.restrictScalars ℚ ℝ (Operator n)
  letI : StarModule ℝ (Operator n) := ⟨by
    intro r x
    change star ((r : ℂ) • x) = r • star x
    rw [star_smul]
    simpa [Complex.star_def] using
      (real_smul_eq_complex_smul r (star x)).symm⟩
  rw [normalizedGibbsCFC_rpow H hH Z s hZ]
  have hsH : IsSelfAdjoint ((s : ℝ) • H) := by
    rw [isSelfAdjoint_iff, star_smul, hH.star_eq]
    simp
  rw [← CFC.real_exp_eq_normedSpace_exp (a := s • H) hsH]
  rw [← cfc_smul_id (R := ℝ) s H]
  rw [← cfc_comp Real.exp (s • ·) H]
  rw [← cfc_const_mul (Z ^ (-s)) (Real.exp ∘ (s • ·)) H]
  rfl

/-- The faithful Gibbs density is the normalized CFC exponential. -/
theorem faithfulGibbsDensity_rho_eq_normalizedGibbsCFC
    {n : ℕ} (H : Operator n) (hH : IsSelfAdjoint H)
    (hZ : 0 < gibbsPartitionReal H) :
    (faithfulGibbsDensity H hH hZ).rho =
      cfc (normalizedScalarGibbsWeight (gibbsPartitionReal H)) H := by
  letI : NormedAlgebra ℝ (Operator n) :=
    NormedAlgebra.restrictScalars ℝ ℂ (Operator n)
  dsimp [faithfulGibbsDensity, normalizedScalarGibbsWeight]
  rw [← CFC.real_exp_eq_normedSpace_exp (a := H) hH]
  exact (cfc_const_mul (gibbsPartitionReal H)⁻¹ Real.exp H).symm

/-- CFC powers of the faithful density in exponential coordinates. -/
theorem faithfulGibbsDensity_rpow
    {n : ℕ} (H : Operator n) (hH : IsSelfAdjoint H)
    (hZ : 0 < gibbsPartitionReal H) (s : ℝ) :
    (faithfulGibbsDensity H hH hZ).rpow s =
      gibbsPartitionReal H ^ (-s) •
        NormedSpace.exp (s • H) := by
  unfold FaithfulDensityOperator.rpow
  rw [faithfulGibbsDensity_rho_eq_normalizedGibbsCFC H hH hZ]
  exact normalizedGibbsCFC_rpow_eq_smul_exp
    H hH (gibbsPartitionReal H) s hZ

/-- The faithful Gibbs real-power path is continuous. -/
theorem continuous_faithfulGibbsDensity_rpow
    {n : ℕ} (H : Operator n) (hH : IsSelfAdjoint H)
    (hZ : 0 < gibbsPartitionReal H) :
    Continuous (faithfulGibbsDensity H hH hZ).rpow := by
  letI : NormedSpace ℝ (Operator n) :=
    NormedSpace.restrictScalars ℝ ℂ (Operator n)
  letI : NormedAlgebra ℝ (Operator n) :=
    NormedAlgebra.restrictScalars ℝ ℂ (Operator n)
  letI : NormedAlgebra ℚ (Operator n) :=
    NormedAlgebra.restrictScalars ℚ ℝ (Operator n)
  rw [show
    (faithfulGibbsDensity H hH hZ).rpow =
      fun s : ℝ =>
        gibbsPartitionReal H ^ (-s) •
          NormedSpace.exp (s • H) by
      funext s
      exact faithfulGibbsDensity_rpow H hH hZ s]
  fun_prop (disch := positivity)

end InfoGeometry.Canonical.NoncommutativeGibbsFaithfulNormalizationBridge
