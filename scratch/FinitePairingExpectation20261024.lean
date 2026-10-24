/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.FinitePairingReducedVacuum

/-! # First-factor expectation of the finite pairing vacuum

The identity holds for arbitrary complex observables and real coefficients,
without normalization. Together with the native reduced positivity and trace
formula, c² + s² = 1 gives a normalized positive state on the first factor.
This scratch candidate has not been kernel checked.
-/
namespace InfoGeometry.OperatorAlgebra.FinitePairingExpectation

open scoped Kronecker
open InfoGeometry.MajoranaPfaffianNaturalClosure
open InfoGeometry.QuantumContext.MatrixStagePartialTrace
open FinitePairingImplementer FinitePairingReducedVacuum

/-- Read an arbitrary first-factor observable through the native ordinary
partial trace; its off-diagonal entries have zero expectation. -/
theorem firstFactor_expectation (c s : ℝ) (X : M2C) :
    Matrix.trace ((X ⊗ₖ (1 : M2C)) *
      (rotor b₁ B₁ b₂ B₂ c s * vacuum *
        (rotor b₁ B₁ b₂ B₂ c s).conjTranspose)) =
      (c : ℂ) ^ 2 * X 0 0 + (s : ℂ) ^ 2 * X 1 1 := by
  rw [← trace_mul_partialTraceSecondOp, reducedVacuum]
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two,
    a, A, annihilationR, creationR, RCLike.real_smul_eq_coe_mul]
  <;> ring

end InfoGeometry.OperatorAlgebra.FinitePairingExpectation
