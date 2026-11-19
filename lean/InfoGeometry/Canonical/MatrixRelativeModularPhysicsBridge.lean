/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.MatrixRelativeModular
import InfoGeometry.Canonical.ArakiItakuraSaitoEquivalence
import InfoGeometry.Canonical.MatrixGeneralizedGibbs
import InfoGeometry.Physics.FiniteRelativeModularOperator

/-!
# The analytic modular matrix and the existing regular-bimodule owner

The concrete positive matrix representation implements the preexisting finite
relative multiplication operator with its right factor set to the native
matrix inverse. Its information-divergence kernel is exactly the existing
operator Itakura--Saito expression with the supplied logarithmic datum replaced
by the native CFC logarithm. The analytic logarithm and expectation theorems
remain owned by `MatrixRelativeModular`.

The final theorem inserts this actual modular expectation into the existing
generalized Gibbs charge/entropy balance. Its reference is the native matrix
Gibbs state of a real vector of parameters paired with Hermitian charges;
neither the charges nor the comparison state are assumed to commute.
-/

noncomputable section

namespace InfoGeometry.Canonical.MatrixRelativeModular

open Matrix
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

local instance {m : Type*} [Fintype m] [DecidableEq m] :
    NormedAlgebra ℝ (Matrix m m 𝕜) where
  norm_smul_le r A := by
    rw [← IsScalarTower.algebraMap_smul 𝕜 r A]
    simpa only [norm_algebraMap'] using
      (norm_smul_le (algebraMap ℝ 𝕜 r) A)

/-- Exact compatibility with the existing regular-bimodule endomorphism. -/
theorem relativeModularMatrix_mulVec_eq_regularBimodule
    (rho sigma X : Matrix n n 𝕜) :
    relativeModularMatrix rho sigma *ᵥ X.vec =
      (Physics.FiniteRelativeModularOperator.relativeModularOperator
        (R := 𝕜) sigma rho⁻¹ X).vec := by
  rw [relativeModularMatrix_mulVec,
    Physics.FiniteRelativeModularOperator.relativeModularOperator_apply]

/-- The analytic information-divergence kernel implements the existing
operator expression with the actual CFC logarithm. -/
theorem itakuraSaitoOperator_eq_existing (A : Matrix (n × n) (n × n) 𝕜) :
    itakuraSaitoOperator A =
      ArakiItakuraSaitoEquivalence.operatorItakuraSaito A (CFC.log A) := by
  exact (ArakiItakuraSaitoEquivalence.operatorItakuraSaito_eq_centered
    A (CFC.log A)).symm

/-- The existing operator Itakura--Saito expression, instantiated by the
concrete relative modular matrix and actual logarithm, has the relative
entropy expectation. -/
theorem squareRootExpectation_existingItakuraSaito_eq_relativeLogTrace
    (rho sigma : Matrix n n 𝕜)
    (hrho : IsStrictlyPositive rho) (hsigma : IsStrictlyPositive sigma)
    (htrho : Matrix.trace rho = 1) (htsigma : Matrix.trace sigma = 1) :
    squareRootExpectation rho
      (ArakiItakuraSaitoEquivalence.operatorItakuraSaito
        (relativeModularMatrix rho sigma) (CFC.log (relativeModularMatrix rho sigma))) =
      Matrix.trace (rho * (CFC.log rho - CFC.log sigma)) := by
  rw [← itakuraSaitoOperator_eq_existing]
  exact squareRootExpectation_itakuraSaito_eq_relativeLogTrace rho sigma
    hrho hsigma htrho htsigma

section GeneralizedGibbs

open MatrixGeneralizedGibbs MatrixGibbsEntropy MatrixEntropyUnitaryOrbit

/-- The generalized Gibbs balance with its relative-entropy defect realized
as the actual modular Itakura--Saito expectation. -/
theorem gibbs_charge_entropy_balance_modular
    {ι : Type*} [Fintype ι] [Nonempty n]
    (Q : ι → Matrix n n ℂ) (hQ : ∀ a, (Q a).IsHermitian) (β : ι → ℝ)
    (rho : Matrix n n ℂ) (hrho : IsStrictlyPositive rho)
    (htrho : Matrix.trace rho = 1) :
    let sigma := normalizedGibbsDensity
      (chargePencil Q β) (chargePencil_isHermitian Q hQ β) 1
    (∑ a, β a * ((Matrix.trace (rho * Q a)).re -
      (Matrix.trace (sigma * Q a)).re)) =
      matrixEntropy rho - matrixEntropy sigma +
        (squareRootExpectation rho
          (ArakiItakuraSaitoEquivalence.operatorItakuraSaito
            (relativeModularMatrix rho sigma)
            (CFC.log (relativeModularMatrix rho sigma)))).re := by
  dsimp only
  rw [squareRootExpectation_existingItakuraSaito_eq_relativeLogTrace
    rho _ hrho (normalizedGibbsDensity_isStrictlyPositive _ _ _)
    htrho (trace_normalizedGibbsDensity _ _ _)]
  exact gibbs_charge_entropy_balance Q hQ β rho htrho

end GeneralizedGibbs

end InfoGeometry.Canonical.MatrixRelativeModular
