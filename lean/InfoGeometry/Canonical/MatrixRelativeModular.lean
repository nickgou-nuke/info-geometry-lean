/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.MatrixRelativeEntropy
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.Vec

/-!
# The finite relative modular operator and its information divergence

For arbitrary strictly positive matrices `rho` and `sigma`, column vectorization
represents `X ↦ sigma * X * rho⁻¹` by `rho⁻¹ᵀ ⊗ₖ sigma`. This is a positive
definite matrix on the full Hilbert--Schmidt carrier, without any commutation
hypothesis on the two states.

The native CFC logarithm is proved by exponentiating the commuting left and
right multiplication generators. In particular, the logarithm formula is not
part of the input data. Pairing the actual modular operator and its actual
logarithm with the vectorized CFC square root of `rho` gives the trace formulas
for Umegaki relative entropy. The expectation of `Delta - 1 - log Delta` equals
that relative entropy for trace-one states.

All structural results are over `RCLike`, so they apply directly to real
symmetric positive definite matrices as well as to complex Hermitian matrices.
The final complex specialization reuses the full-matrix Klein inequality from
`MatrixRelativeEntropy`.
-/

noncomputable section

namespace InfoGeometry.Canonical.MatrixRelativeModular

open Matrix
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder Kronecker

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

local instance {m : Type*} [Fintype m] [DecidableEq m] :
    NormedAlgebra ℝ (Matrix m m 𝕜) where
  norm_smul_le r A := by
    rw [← IsScalarTower.algebraMap_smul 𝕜 r A]
    simpa only [norm_algebraMap'] using
      (norm_smul_le (algebraMap ℝ 𝕜 r) A)

local instance {m : Type*} [Fintype m] [DecidableEq m] :
    NormedAlgebra ℚ (Matrix m m 𝕜) where
  norm_smul_le r A := by
    rw [← IsScalarTower.algebraMap_smul 𝕜 r A]
    simpa only [norm_algebraMap'] using
      (norm_smul_le (algebraMap ℚ 𝕜 r) A)

local notation "Mat" => Matrix n n 𝕜
local notation "Super" => Matrix (n × n) (n × n) 𝕜

/-- The concrete relative modular matrix in column-vectorization coordinates. -/
def relativeModularMatrix (rho sigma : Mat) : Super :=
  rho⁻¹ᵀ ⊗ₖ sigma

/-- The full Hilbert--Schmidt action, retaining the order of both factors. -/
theorem relativeModularMatrix_mulVec (rho sigma X : Mat) :
    relativeModularMatrix rho sigma *ᵥ X.vec = (sigma * X * rho⁻¹).vec := by
  simp only [relativeModularMatrix, Matrix.kronecker_mulVec_vec,
    Matrix.transpose_transpose]

/-- Strict positivity on the full vectorized matrix carrier. -/
theorem relativeModularMatrix_posDef (rho sigma : Mat)
    (hrho : IsStrictlyPositive rho) (hsigma : IsStrictlyPositive sigma) :
    (relativeModularMatrix rho sigma).PosDef := by
  exact (Matrix.isStrictlyPositive_iff_posDef.mp hrho).inv.transpose.kronecker
    (Matrix.isStrictlyPositive_iff_posDef.mp hsigma)

/-- Native CFC strict positivity of the relative modular matrix. -/
theorem relativeModularMatrix_isStrictlyPositive (rho sigma : Mat)
    (hrho : IsStrictlyPositive rho) (hsigma : IsStrictlyPositive sigma) :
    IsStrictlyPositive (relativeModularMatrix rho sigma) :=
  Matrix.isStrictlyPositive_iff_posDef.mpr
    (relativeModularMatrix_posDef rho sigma hrho hsigma)

private def tensorLeft : Mat →ₐ[𝕜] Super where
  toFun A := A ⊗ₖ (1 : Mat)
  map_one' := Matrix.one_kronecker_one
  map_mul' A B := by
    simpa only [Matrix.one_mul] using
      (Matrix.mul_kronecker_mul A B (1 : Mat) (1 : Mat))
  map_zero' := Matrix.zero_kronecker _
  map_add' A B := Matrix.add_kronecker A B _
  commutes' r := by
    simp only [Algebra.algebraMap_eq_smul_one, Matrix.smul_kronecker,
      Matrix.one_kronecker_one]

private def tensorRight : Mat →ₐ[𝕜] Super where
  toFun A := (1 : Mat) ⊗ₖ A
  map_one' := Matrix.one_kronecker_one
  map_mul' A B := by
    simpa only [Matrix.one_mul] using
      (Matrix.mul_kronecker_mul (1 : Mat) (1 : Mat) A B)
  map_zero' := Matrix.kronecker_zero _
  map_add' A B := Matrix.kronecker_add _ A B
  commutes' r := by
    simp only [Algebra.algebraMap_eq_smul_one, Matrix.kronecker_smul,
      Matrix.one_kronecker_one]

private theorem exp_tensorLeft (A : Mat) :
    NormedSpace.exp (A ⊗ₖ (1 : Mat)) = NormedSpace.exp A ⊗ₖ (1 : Mat) := by
  have hcont : Continuous (tensorLeft (𝕜 := 𝕜) (n := n)) :=
    (tensorLeft (𝕜 := 𝕜) (n := n)).toLinearMap.continuous_of_finiteDimensional
  exact (NormedSpace.map_exp (tensorLeft (𝕜 := 𝕜) (n := n)) hcont A).symm

private theorem exp_tensorRight (A : Mat) :
    NormedSpace.exp ((1 : Mat) ⊗ₖ A) = (1 : Mat) ⊗ₖ NormedSpace.exp A := by
  have hcont : Continuous (tensorRight (𝕜 := 𝕜) (n := n)) :=
    (tensorRight (𝕜 := 𝕜) (n := n)).toLinearMap.continuous_of_finiteDimensional
  exact (NormedSpace.map_exp (tensorRight (𝕜 := 𝕜) (n := n)) hcont A).symm

private theorem tensor_factors_commute (A B : Mat) :
    Commute ((1 : Mat) ⊗ₖ A) (B ⊗ₖ (1 : Mat)) := by
  change ((1 : Mat) ⊗ₖ A) * (B ⊗ₖ (1 : Mat)) =
    (B ⊗ₖ (1 : Mat)) * ((1 : Mat) ⊗ₖ A)
  simp only [← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]

/-- The generator of left logarithmic multiplication minus right logarithmic
multiplication. The two summands commute on the matrix carrier. -/
def modularLogGenerator (rho sigma : Mat) : Super :=
  (1 : Mat) ⊗ₖ CFC.log sigma + (-(CFC.log rho))ᵀ ⊗ₖ (1 : Mat)

theorem modularLogGenerator_isSelfAdjoint (rho sigma : Mat) :
    IsSelfAdjoint (modularLogGenerator rho sigma) := by
  have hleft : (CFC.log sigma).IsHermitian :=
    (IsSelfAdjoint.log (a := sigma)).isHermitian
  have hright : (-(CFC.log rho))ᵀ.IsHermitian :=
    (IsSelfAdjoint.log (a := rho)).neg.isHermitian.transpose
  change (modularLogGenerator rho sigma).IsHermitian
  simp only [modularLogGenerator, Matrix.IsHermitian, Matrix.conjTranspose_add,
    Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, hleft.eq, hright.eq]

set_option maxHeartbeats 800000 in
/-- Exponentiation identifies the logarithmic generator with the actual
relative modular operator. -/
theorem exp_modularLogGenerator (rho sigma : Mat)
    (hrho : IsStrictlyPositive rho) (hsigma : IsStrictlyPositive sigma) :
    NormedSpace.exp (modularLogGenerator rho sigma) = relativeModularMatrix rho sigma := by
  rw [modularLogGenerator,
    NormedSpace.exp_add_of_commute (tensor_factors_commute _ _),
    exp_tensorRight, exp_tensorLeft, Matrix.exp_transpose, Matrix.exp_neg,
    CFC.exp_log rho hrho, CFC.exp_log sigma hsigma]
  simp only [← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one,
    relativeModularMatrix]

/-- The native CFC logarithm, derived without a joint eigenbasis assumption. -/
theorem log_relativeModularMatrix (rho sigma : Mat)
    (hrho : IsStrictlyPositive rho) (hsigma : IsStrictlyPositive sigma) :
    CFC.log (relativeModularMatrix rho sigma) = modularLogGenerator rho sigma := by
  rw [← exp_modularLogGenerator rho sigma hrho hsigma,
    CFC.log_exp _ (modularLogGenerator_isSelfAdjoint rho sigma)]

/-- The actual logarithm acts as `log sigma * X - X * log rho`. -/
theorem log_relativeModularMatrix_mulVec (rho sigma X : Mat)
    (hrho : IsStrictlyPositive rho) (hsigma : IsStrictlyPositive sigma) :
    CFC.log (relativeModularMatrix rho sigma) *ᵥ X.vec =
      (CFC.log sigma * X - X * CFC.log rho).vec := by
  rw [log_relativeModularMatrix rho sigma hrho hsigma]
  simp only [modularLogGenerator, Matrix.add_mulVec, Matrix.kronecker_mulVec_vec,
    Matrix.transpose_one, Matrix.transpose_transpose, Matrix.one_mul,
    Matrix.mul_one, Matrix.mul_neg, Matrix.vec_add, Matrix.vec_neg,
    sub_eq_add_neg]

/-- The state vector in the Hilbert--Schmidt carrier. -/
def squareRootVector (rho : Mat) : n × n → 𝕜 := (CFC.sqrt rho).vec

/-- Hilbert--Schmidt vector expectation at the actual CFC square root. -/
def squareRootExpectation (rho : Mat) (A : Super) : 𝕜 :=
  star (squareRootVector rho) ⬝ᵥ (A *ᵥ squareRootVector rho)

/-- The finite-sum pairing is exactly the native Euclidean inner product on
the vectorized Hilbert--Schmidt carrier. -/
theorem squareRootExpectation_eq_inner (rho : Mat) (A : Super) :
    squareRootExpectation rho A =
      inner 𝕜 (WithLp.toLp 2 (squareRootVector rho))
        (WithLp.toLp 2 (A *ᵥ squareRootVector rho)) := by
  rw [squareRootExpectation, EuclideanSpace.inner_toLp_toLp]
  exact dotProduct_comm _ _

theorem squareRootExpectation_sub (rho : Mat) (A B : Super) :
    squareRootExpectation rho (A - B) =
      squareRootExpectation rho A - squareRootExpectation rho B := by
  simp only [squareRootExpectation, Matrix.sub_mulVec, dotProduct_sub]

private theorem sqrt_conjTranspose (rho : Mat) :
    (CFC.sqrt rho)ᴴ = CFC.sqrt rho :=
  (CFC.sqrt_nonneg rho).isSelfAdjoint.isHermitian.eq

/-- The squared Hilbert--Schmidt norm of the square-root state is its trace. -/
theorem squareRootVector_inner_self (rho : Mat) (hrho : IsStrictlyPositive rho) :
    star (squareRootVector rho) ⬝ᵥ squareRootVector rho = Matrix.trace rho := by
  simp only [squareRootVector, Matrix.star_vec_dotProduct_vec, sqrt_conjTranspose,
    CFC.sqrt_mul_sqrt_self rho hrho.nonneg]

theorem squareRootExpectation_one (rho : Mat) (hrho : IsStrictlyPositive rho) :
    squareRootExpectation rho 1 = Matrix.trace rho := by
  simp only [squareRootExpectation, Matrix.one_mulVec,
    squareRootVector_inner_self rho hrho]

private theorem sqrt_inv_sqrt (rho : Mat) (hrho : IsStrictlyPositive rho) :
    CFC.sqrt rho * rho⁻¹ * CFC.sqrt rho = (1 : Mat) := by
  have hunit : IsUnit rho.det := (Matrix.isUnit_iff_isUnit_det rho).mp hrho.isUnit
  have hcomm : Commute rho rho⁻¹ := by
    change rho * rho⁻¹ = rho⁻¹ * rho
    rw [Matrix.mul_nonsing_inv rho hunit, Matrix.nonsing_inv_mul rho hunit]
  have hscomm : Commute (CFC.sqrt rho) rho⁻¹ := hcomm.cfcₙ_nnreal NNReal.sqrt
  rw [hscomm.eq, Matrix.mul_assoc, CFC.sqrt_mul_sqrt_self rho hrho.nonneg,
    Matrix.nonsing_inv_mul rho hunit]

/-- The expectation of the actual relative modular operator is the reference
trace, with no commutativity assumption on the two states. -/
theorem squareRootExpectation_relativeModularMatrix (rho sigma : Mat)
    (hrho : IsStrictlyPositive rho) :
    squareRootExpectation rho (relativeModularMatrix rho sigma) = Matrix.trace sigma := by
  simp only [squareRootExpectation, squareRootVector, relativeModularMatrix_mulVec,
    Matrix.star_vec_dotProduct_vec, sqrt_conjTranspose]
  calc
    Matrix.trace (CFC.sqrt rho * (sigma * CFC.sqrt rho * rho⁻¹)) =
        Matrix.trace (sigma * (CFC.sqrt rho * rho⁻¹ * CFC.sqrt rho)) := by
      rw [Matrix.trace_mul_comm (CFC.sqrt rho) _]
      simp only [Matrix.mul_assoc]
    _ = Matrix.trace ((CFC.sqrt rho * rho⁻¹ * CFC.sqrt rho) * sigma) :=
      Matrix.trace_mul_comm _ _
    _ = Matrix.trace sigma := by rw [sqrt_inv_sqrt rho hrho, Matrix.one_mul]

private theorem trace_sqrt_sandwich (rho A : Mat) (hrho : IsStrictlyPositive rho) :
    Matrix.trace (CFC.sqrt rho * (A * CFC.sqrt rho)) = Matrix.trace (rho * A) := by
  rw [← Matrix.mul_assoc, Matrix.trace_mul_cycle,
    CFC.sqrt_mul_sqrt_self rho hrho.nonneg]

/-- Negative log-modular expectation is the full matrix relative-log trace. -/
theorem neg_squareRootExpectation_log (rho sigma : Mat)
    (hrho : IsStrictlyPositive rho) (hsigma : IsStrictlyPositive sigma) :
    -squareRootExpectation rho (CFC.log (relativeModularMatrix rho sigma)) =
      Matrix.trace (rho * (CFC.log rho - CFC.log sigma)) := by
  simp only [squareRootExpectation, squareRootVector,
    log_relativeModularMatrix_mulVec rho sigma _ hrho hsigma,
    Matrix.star_vec_dotProduct_vec, sqrt_conjTranspose]
  rw [Matrix.mul_sub, Matrix.trace_sub, trace_sqrt_sandwich rho _ hrho,
    ← Matrix.mul_assoc, CFC.sqrt_mul_sqrt_self rho hrho.nonneg,
    Matrix.mul_sub, Matrix.trace_sub]
  exact neg_sub _ _

/-- The operator counterpart of the scalar Itakura--Saito kernel `x - 1 - log x`. -/
def itakuraSaitoOperator (A : Super) : Super := A - 1 - CFC.log A

/-- The native CFC Itakura--Saito operator is positive semidefinite. -/
theorem itakuraSaitoOperator_nonneg (A : Super) (hA : IsStrictlyPositive A) :
    0 ≤ itakuraSaitoOperator A := by
  have hlog : ContinuousOn Real.log (spectrum ℝ A) :=
    Real.continuousOn_log.mono fun x hx => (hA.spectrum_pos hx).ne'
  have hrepr : cfc (fun x : ℝ => x - 1 - Real.log x) A =
      itakuraSaitoOperator A := by
    rw [cfc_sub (fun x : ℝ => x - 1) Real.log A (by fun_prop) hlog,
      cfc_sub (fun x : ℝ => x) (fun _ : ℝ => 1) A,
      cfc_id' ℝ A hA.nonneg.isSelfAdjoint,
      cfc_const_one ℝ A hA.nonneg.isSelfAdjoint]
    rfl
  rw [← hrepr]
  exact cfc_nonneg fun x hx =>
    sub_nonneg.mpr (Real.log_le_sub_one_of_pos (hA.spectrum_pos hx))

/-- The general trace correction before normalizing either state. -/
theorem squareRootExpectation_itakuraSaito (rho sigma : Mat)
    (hrho : IsStrictlyPositive rho) (hsigma : IsStrictlyPositive sigma) :
    squareRootExpectation rho (itakuraSaitoOperator (relativeModularMatrix rho sigma)) =
      Matrix.trace sigma - Matrix.trace rho +
        Matrix.trace (rho * (CFC.log rho - CFC.log sigma)) := by
  rw [itakuraSaitoOperator, squareRootExpectation_sub, squareRootExpectation_sub,
    squareRootExpectation_relativeModularMatrix rho sigma hrho,
    squareRootExpectation_one rho hrho, sub_eq_add_neg,
    neg_squareRootExpectation_log rho sigma hrho hsigma]

/-- For trace-one states, the actual modular Itakura--Saito expectation is
exactly the Umegaki relative-log trace. -/
theorem squareRootExpectation_itakuraSaito_eq_relativeLogTrace (rho sigma : Mat)
    (hrho : IsStrictlyPositive rho) (hsigma : IsStrictlyPositive sigma)
    (htrho : Matrix.trace rho = 1) (htsigma : Matrix.trace sigma = 1) :
    squareRootExpectation rho (itakuraSaitoOperator (relativeModularMatrix rho sigma)) =
      Matrix.trace (rho * (CFC.log rho - CFC.log sigma)) := by
  rw [squareRootExpectation_itakuraSaito rho sigma hrho hsigma, htrho, htsigma]
  simp only [sub_self, zero_add]

/-- Positivity of the modular information-divergence expectation holds over
both real and complex scalars. -/
theorem squareRootExpectation_itakuraSaito_nonneg (rho sigma : Mat)
    (hrho : IsStrictlyPositive rho) (hsigma : IsStrictlyPositive sigma) :
    0 ≤ squareRootExpectation rho
      (itakuraSaitoOperator (relativeModularMatrix rho sigma)) := by
  exact (itakuraSaitoOperator_nonneg _
    (relativeModularMatrix_isStrictlyPositive rho sigma hrho hsigma)).posSemidef
      |>.dotProduct_mulVec_nonneg _

/-- The real full-matrix relative entropy is nonnegative. This uses the
positive modular kernel directly and requires no complex scalar extension. -/
theorem real_relativeLogTrace_nonneg (rho sigma : Matrix n n ℝ)
    (hrho : IsStrictlyPositive rho) (hsigma : IsStrictlyPositive sigma)
    (htrho : Matrix.trace rho = 1) (htsigma : Matrix.trace sigma = 1) :
    0 ≤ Matrix.trace (rho * (CFC.log rho - CFC.log sigma)) := by
  rw [← squareRootExpectation_itakuraSaito_eq_relativeLogTrace rho sigma
    hrho hsigma htrho htsigma]
  exact squareRootExpectation_itakuraSaito_nonneg rho sigma hrho hsigma

/-- Direct agreement with the complex relative entropy proved by the existing
full-matrix Klein owner. -/
theorem complex_modularExpectation_nonneg (rho sigma : Matrix n n ℂ)
    (hrho : IsStrictlyPositive rho) (hsigma : IsStrictlyPositive sigma)
    (htrho : Matrix.trace rho = 1) (htsigma : Matrix.trace sigma = 1) :
    0 ≤ (squareRootExpectation rho
      (itakuraSaitoOperator (relativeModularMatrix rho sigma))).re := by
  rw [squareRootExpectation_itakuraSaito_eq_relativeLogTrace rho sigma
    hrho hsigma htrho htsigma]
  exact MatrixRelativeEntropy.relativeLogTrace_nonneg rho sigma hrho hsigma htrho htsigma

end InfoGeometry.Canonical.MatrixRelativeModular
