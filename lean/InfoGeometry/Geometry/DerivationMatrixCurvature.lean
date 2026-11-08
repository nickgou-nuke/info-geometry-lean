/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.DerivationCurvatureVariation
import InfoGeometry.Geometry.MatrixCurvatureHessian
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! # Sampling native derivation forms into full matrix connection calculus

The finite list of Lie directions need not commute. Its bracket correction
is kept explicitly in both curvature and its first variation. Sampling is
a linear map of the actual one-cochain carrier, not a new connection axiom.
-/

noncomputable section

namespace InfoGeometry.Geometry.DerivationMatrixCurvature

open scoped Matrix Matrix.Norms.L2Operator
open InfoGeometry.Algebra
open InfoGeometry.OperatorAlgebra.DerivationDifferentialForms
open MatrixCurvatureEnergy

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
local notation "Mat" => Matrix n n ℂ


/-- Evaluation on a finite family of actual Lie directions. -/
def sampleOneForm (K : DerivationLieLane ℝ (Matrix n n ℂ)) (v : ι → K.L) : (K.L →ₗ[ℝ] Mat) →ₗ[ℝ] (ι → Mat) where
  toFun Γ i := Γ (v i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Fintype ι] in
@[simp] theorem sampleOneForm_apply (K : DerivationLieLane ℝ (Matrix n n ℂ))
    (v : ι → K.L) (Γ : OneForm K) (i : ι) :
    sampleOneForm K v Γ i = Γ (v i) := rfl

/-- Finite dimensionality makes each represented derivation continuous. -/
def sampledBaseOperator (K : DerivationLieLane ℝ (Matrix n n ℂ)) (v : ι → K.L) (i : ι) : Mat →L[ℝ] Mat :=
  LinearMap.toContinuousLinearMap (K.operatorAction (v i))

omit [Fintype ι] in
@[simp] theorem sampledBaseOperator_apply (K : DerivationLieLane ℝ (Matrix n n ℂ))
    (v : ι → K.L) (i : ι) (a : Mat) :
    sampledBaseOperator K v i a = K.operatorAction (v i) a := rfl

omit [Fintype ι] in
theorem sampledBaseOperator_leibniz (K : DerivationLieLane ℝ (Matrix n n ℂ))
    (v : ι → K.L) (i : ι) (a b : Mat) :
    sampledBaseOperator K v i (a * b) =
      sampledBaseOperator K v i a * b + a * sampledBaseOperator K v i b :=
  K.operatorAction_leibniz (v i) a b

omit [Fintype ι] in
/-- Exact carrier comparison, including the bracket of the sampled directions. -/
theorem connectionCurvature_eq_sampled_curvature
    (K : DerivationLieLane ℝ (Matrix n n ℂ)) (v : ι → K.L)
    (Γ : OneForm K) (i j : ι) :
    connectionCurvature K Γ (v i) (v j) =
      curvatureEntry (sampledBaseOperator K v) (sampleOneForm K v Γ) i j -
        Γ ⁅v i, v j⁆ := by
  simp only [connectionCurvature_apply, curvatureEntry, sampleOneForm_apply,
    sampledBaseOperator_apply]
  noncomm_ring

omit [Fintype ι] in
/-- The algebraic linearization agrees with the actual matrix differential
after its explicit Lie-direction correction. -/
theorem curvatureLinearization_eq_sampled_differential
    (K : DerivationLieLane ℝ (Matrix n n ℂ)) (v : ι → K.L)
    (Γ α : OneForm K) (i j : ι) :
    curvatureLinearization K Γ α (v i) (v j) =
      curvatureDifferential (sampledBaseOperator K v) (sampleOneForm K v Γ)
        i j (sampleOneForm K v α) - α ⁅v i, v j⁆ := by
  simp only [curvatureLinearization_apply, covariantDerivative,
    curvatureDifferential_apply, sampleOneForm_apply, sampledBaseOperator_apply]
  noncomm_ring

/-- The mixed second variation has no bracket correction because that term
is linear in the connection. -/
theorem connectionCrossWedge_eq_sampled_second_differential
    (K : DerivationLieLane ℝ (Matrix n n ℂ)) (v : ι → K.L)
    (α β : OneForm K) (i j : ι) :
    connectionCrossWedge K α β (v i) (v j) =
      curvatureBilinear i j (sampleOneForm K v α) (sampleOneForm K v β) := by
  simp only [connectionCrossWedge_apply, curvatureBilinear_apply, sampleOneForm_apply]
  noncomm_ring

end InfoGeometry.Geometry.DerivationMatrixCurvature
