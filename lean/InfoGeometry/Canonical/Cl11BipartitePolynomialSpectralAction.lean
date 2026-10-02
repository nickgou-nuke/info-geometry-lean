import Mathlib.Tactic

import InfoGeometry.Canonical.Cl11BipartiteSpectralCurvature
import InfoGeometry.Canonical.Cl11BipartiteDiracBridge

/-!
# Finite polynomial spectral action on the bipartite Cl(1,1) stage

This module formalizes a theorem-safe finite polynomial analogue of the
spectral action on the repository-owned stage-two matrix carrier.

For
  P(X) = c₀ I + c₁ X + c₂ X²
we define
  S_P(X) = Tr(P(X)).

Closed here:
* invariance of S_P under arbitrary inner similarity by units;
* exact trace formula for
    X = Δ_L ⊗ I + I ⊗ Δ_R;
* exact mixed trace term
    2 Tr(Δ_L) Tr(Δ_R).

This is a finite polynomial trace identity.  It is not the analytic
Chamseddine--Connes functional Tr(f(D²/Λ²)), nor a Seeley--DeWitt expansion.
No interpretation of the mixed term as mutual information or entanglement
energy is asserted.
-/

noncomputable section

namespace InfoGeometry.Canonical.Cl11BipartitePolynomialSpectralAction

open scoped Matrix Kronecker
open InfoGeometry.Clifford.Cl11Matrix
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Canonical.Cl11BipartiteSpectralCurvature

abbrev Atom := Mat2
abbrev StageOne := MatStage 1
abbrev StageTwo := MatStage 2

/-- Quadratic polynomial cutoff model
    P(X) = c₀ I + c₁ X + c₂ X². -/
def spectralPolynomial (c0 c1 c2 : ℝ) (X : StageTwo) : StageTwo :=
  c0 • (1 : StageTwo) + c1 • X + c2 • (X * X)

/-- Finite polynomial spectral trace. -/
def polynomialSpectralAction (c0 c1 c2 : ℝ) (X : StageTwo) : ℝ :=
  Matrix.trace (spectralPolynomial c0 c1 c2 X)

/-- Conjugation by a stage-two unit. -/
def stageTwoConjugate (U : Units StageTwo) (X : StageTwo) : StageTwo :=
  (U : StageTwo) * X * (↑U⁻¹ : StageTwo)

@[simp] theorem stageTwoConjugate_one (U : Units StageTwo) :
    stageTwoConjugate U 1 = 1 := by
  simp [stageTwoConjugate, mul_assoc]

@[simp] theorem stageTwoConjugate_add
    (U : Units StageTwo) (X Y : StageTwo) :
    stageTwoConjugate U (X + Y) =
      stageTwoConjugate U X + stageTwoConjugate U Y := by
  simp [stageTwoConjugate, add_mul, mul_add]

@[simp] theorem stageTwoConjugate_smul
    (U : Units StageTwo) (r : ℝ) (X : StageTwo) :
    stageTwoConjugate U (r • X) =
      r • stageTwoConjugate U X := by
  simp [stageTwoConjugate, Matrix.mul_smul, Matrix.smul_mul]

@[simp] theorem stageTwoConjugate_mul
    (U : Units StageTwo) (X Y : StageTwo) :
    stageTwoConjugate U (X * Y) =
      stageTwoConjugate U X * stageTwoConjugate U Y := by
  simp [stageTwoConjugate, mul_assoc]

/-- Polynomial functional calculus commutes with inner conjugation. -/
theorem spectralPolynomial_conjugate
    (U : Units StageTwo) (c0 c1 c2 : ℝ) (X : StageTwo) :
    spectralPolynomial c0 c1 c2 (stageTwoConjugate U X) =
      stageTwoConjugate U (spectralPolynomial c0 c1 c2 X) := by
  simp [spectralPolynomial]

/-- Matrix trace is invariant under stage-two unit conjugation. -/
theorem trace_stageTwoConjugate
    (U : Units StageTwo) (X : StageTwo) :
    Matrix.trace (stageTwoConjugate U X) = Matrix.trace X := by
  unfold stageTwoConjugate
  calc
    Matrix.trace ((U : StageTwo) * X * (↑U⁻¹ : StageTwo))
        = Matrix.trace ((X * (↑U⁻¹ : StageTwo)) * (U : StageTwo)) := by
            rw [Matrix.trace_mul_comm]
    _ = Matrix.trace (X * ((↑U⁻¹ : StageTwo) * (U : StageTwo))) := by
            rw [Matrix.mul_assoc]
    _ = Matrix.trace X := by simp

/-- Exact gauge/similarity invariance of the finite polynomial spectral action. -/
theorem polynomialSpectralAction_conjugation_invariant
    (U : Units StageTwo) (c0 c1 c2 : ℝ) (X : StageTwo) :
    polynomialSpectralAction c0 c1 c2 (stageTwoConjugate U X) =
      polynomialSpectralAction c0 c1 c2 X := by
  unfold polynomialSpectralAction
  rw [spectralPolynomial_conjugate]
  exact trace_stageTwoConjugate U (spectralPolynomial c0 c1 c2 X)

/-! ## Decoupled left/right Laplacian readout -/

/-- Tensor-sum operator X = Δ_L ⊗ I + I ⊗ Δ_R. -/
def tensorSum (DeltaL : StageOne) (DeltaR : Atom) : StageTwo :=
  DeltaL ⊗ₖ (1 : Atom) + (1 : StageOne) ⊗ₖ DeltaR

/-- Exact square of the tensor sum. -/
theorem tensorSum_sq (DeltaL : StageOne) (DeltaR : Atom) :
    tensorSum DeltaL DeltaR * tensorSum DeltaL DeltaR =
      (DeltaL * DeltaL) ⊗ₖ (1 : Atom) +
      (2 : ℝ) • (DeltaL ⊗ₖ DeltaR) +
      (1 : StageOne) ⊗ₖ (DeltaR * DeltaR) := by
  unfold tensorSum
  rw [add_mul, mul_add, mul_add]
  repeat rw [Matrix.mul_kronecker_mul]
  simp only [Matrix.mul_one, Matrix.one_mul]
  module

/-- Trace of the stage-one identity is 2. -/
theorem trace_stageOne_one :
    Matrix.trace (1 : StageOne) = 2 := by
  rw [Matrix.trace_one]
  norm_num [InfoGeometry.Clifford.TowerMatrix.idx_card_pow_two]

/-- Trace of the Cl(1,1) atom identity is 2. -/
theorem trace_atom_one :
    Matrix.trace (1 : Atom) = 2 := by
  rw [Matrix.trace_one]
  norm_num

/-- Trace of the stage-two identity is 4. -/
theorem trace_stageTwo_one :
    Matrix.trace (1 : StageTwo) = 4 := by
  rw [Matrix.trace_one]
  norm_num [InfoGeometry.Clifford.TowerMatrix.idx_card_pow_two]

/-- Exact trace of the tensor-sum operator. -/
theorem trace_tensorSum (DeltaL : StageOne) (DeltaR : Atom) :
    Matrix.trace (tensorSum DeltaL DeltaR) =
      2 * (Matrix.trace DeltaL + Matrix.trace DeltaR) := by
  unfold tensorSum
  rw [Matrix.trace_add, Matrix.trace_kronecker, Matrix.trace_kronecker,
    trace_atom_one, trace_stageOne_one]
  ring

/-- Exact trace of the squared tensor sum, including the mixed term. -/
theorem trace_tensorSum_sq (DeltaL : StageOne) (DeltaR : Atom) :
    Matrix.trace (tensorSum DeltaL DeltaR * tensorSum DeltaL DeltaR) =
      2 * (Matrix.trace (DeltaL * DeltaL) +
        Matrix.trace DeltaL * Matrix.trace DeltaR +
        Matrix.trace (DeltaR * DeltaR)) := by
  rw [tensorSum_sq]
  rw [Matrix.trace_add, Matrix.trace_add, Matrix.trace_smul,
    Matrix.trace_kronecker, Matrix.trace_kronecker, Matrix.trace_kronecker,
    trace_atom_one, trace_stageOne_one]
  ring

/-- Exact finite polynomial spectral-action decomposition on the tensor sum. -/
theorem polynomialSpectralAction_tensorSum
    (c0 c1 c2 : ℝ) (DeltaL : StageOne) (DeltaR : Atom) :
    polynomialSpectralAction c0 c1 c2 (tensorSum DeltaL DeltaR) =
      4 * c0 +
      2 * c1 * (Matrix.trace DeltaL + Matrix.trace DeltaR) +
      2 * c2 *
        (Matrix.trace (DeltaL * DeltaL) +
          Matrix.trace DeltaL * Matrix.trace DeltaR +
          Matrix.trace (DeltaR * DeltaR)) := by
  unfold polynomialSpectralAction spectralPolynomial
  rw [Matrix.trace_add, Matrix.trace_add, Matrix.trace_smul,
    Matrix.trace_smul, Matrix.trace_smul, trace_stageTwo_one,
    trace_tensorSum, trace_tensorSum_sq]
  ring

/-- The mixed quadratic contribution is exactly
    2 c₂ Tr(Δ_L) Tr(Δ_R). -/
theorem mixed_quadratic_trace_term
    (c2 : ℝ) (DeltaL : StageOne) (DeltaR : Atom) :
    2 * c2 * (Matrix.trace DeltaL * Matrix.trace DeltaR) =
      c2 * Matrix.trace ((2 : ℝ) • (DeltaL ⊗ₖ DeltaR)) := by
  rw [Matrix.trace_smul, Matrix.trace_kronecker]
  ring

end InfoGeometry.Canonical.Cl11BipartitePolynomialSpectralAction
