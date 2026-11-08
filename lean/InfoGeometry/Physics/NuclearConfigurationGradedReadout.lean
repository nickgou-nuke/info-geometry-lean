/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.NuclearConfigurationOperatorLift

/-!
# Exact projected spectroscopy and its full-Hamiltonian boundary

The existing QPNM block lifts to `P H P` on the common five-grade carrier.
Finite transition readouts agree exactly after lifting. The full Hamiltonian
has an explicit level-two leakage, preventing an unwarranted inference of
full eigenvectors from the finite compressed spectral calculation.
-/

noncomputable section

namespace InfoGeometry.Physics.NuclearConfigurationGradedReadout

open Matrix
open InfoGeometry.Physics.NuclearFiveGradeCommonCarrierRepresentation
open InfoGeometry.Physics.NuclearFiveGradeSolovievCommonCompression
open InfoGeometry.Physics.NuclearConfigurationMixing
open InfoGeometry.Physics.NuclearConfigurationOperatorLift
open InfoGeometry.Physics.SolovievTransitionStrength
open InfoGeometry.Physics.SolovievQPNMEigenproblem
open InfoGeometry.Topology.KatzSarnakRandomMatrixBridge

local notation "M2" => InfoGeometry.Algebra.FiniteSpin.Mat2R

theorem cornerLift_qpnm_eq_projected (Eqp omega V : ℝ) :
    cornerLift (qpnmMatrix Eqp omega V) =
      modelProjection * fullHamiltonian Eqp omega V * modelProjection := by
  apply LinearMap.ext
  intro ψ
  let v := modelReadout ψ
  have hv : ![v 0, v 1] = v := by ext i; fin_cases i <;> rfl
  have h := projected_fullHamiltonian_on_model Eqp omega V (v 0) (v 1)
  rw [hv, modelProjection_modelEmbed] at h
  exact h.symm

/-- Finite eigen-equations lift exactly to the corner operator. -/
theorem lifted_eigen_equation_iff (H : M2) (v : ModelVector) (E : ℝ) :
    cornerLift H (modelEmbed v) = E • modelEmbed v ↔ H.mulVec v = E • v := by
  rw [cornerLift_modelEmbed]
  constructor
  · intro h
    have hr := congrArg modelReadout h
    simpa using hr
  · intro h
    rw [h, map_smul]

/-- The concrete spectral model of PR #220 has the same lifted eigen-equation. -/
theorem lifted_spectral_first (e₁ e₂ c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
    cornerLift (spectralHamiltonian e₁ e₂ c s) (modelEmbed ![c, s]) =
      e₁ • modelEmbed ![c, s] := by
  apply (lifted_eigen_equation_iff _ _ _).mpr
  exact spectralHamiltonian_first_eigenpair e₁ e₂ c s h

theorem lifted_transition_readout (O : M2) (initial final : ModelVector) :
    dotProduct final (modelReadout (cornerLift O (modelEmbed initial))) =
      amplitude O initial final := by
  simp [amplitude]

/-- A full-carrier two-sided transform restricts to the matrix transpose sandwich.
For an orthogonal `Q`, this is conjugation by the completed basis change. -/
theorem completed_conjugation_readout (O Q : M2) :
    modelMatrix (completedLift Q * cornerLift O * completedLift Qᵀ) =
      Q * O * Qᵀ := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  change (modelMatrix (completedLift Q * cornerLift O * completedLift Qᵀ)).mulVec v =
    (Q * O * Qᵀ).mulVec v
  simp only [modelMatrix_mulVec, Module.End.mul_apply, completedLift_modelEmbed,
    cornerLift_modelEmbed, modelReadout_modelEmbed, Matrix.mulVec_mulVec, mul_assoc]

/-- Coupling to a phonon creates a level-two component from the one-phonon
coordinate. This component is discarded by the model projection. -/
theorem fullHamiltonian_level_two (Eqp omega V C D : ℝ) :
    (fullHamiltonian Eqp omega V (modelEmbed ![C, D]) 2 2).a = V * D := by
  simp [fullHamiltonian, quasiparticleNumber, representation, occupationLift,
    fermionAction, phononNumber, phononCreation, phononAnnihilation,
    modelEmbed, quasiparticleKet, scalarCoefficient, Module.End.mul_apply,
    InfoGeometry.Algebra.ZornVectorMatrix.add,
    InfoGeometry.Algebra.ZornVectorMatrix.smul,
    InfoGeometry.Algebra.ZornVectorMatrix.zero]
  right
  change ((4 : ℕ) • (0 : Coefficient)).a = 0
  rw [nsmul_zero]
  rfl

/-- The full operator is not the corner lift when the phonon coupling is nonzero. -/
theorem fullHamiltonian_ne_cornerLift (Eqp omega V : ℝ) (hV : V ≠ 0) :
    fullHamiltonian Eqp omega V ≠ cornerLift (qpnmMatrix Eqp omega V) := by
  intro h
  have hread := congrArg (fun T : Operator => (T (modelEmbed ![0, 1]) 2 2).a) h
  rw [fullHamiltonian_level_two] at hread
  apply hV
  simpa [modelEmbed, InfoGeometry.Algebra.ZornVectorMatrix.zero] using hread

/-- Stronger leakage boundary: at nonzero coupling, no nonzero vector wholly
inside the two-channel model is an eigenvector of the uncompressed operator. -/
theorem full_eigen_equation_forces_zero (Eqp omega V E : ℝ) (C D : ℝ)
    (hV : V ≠ 0)
    (heig : fullHamiltonian Eqp omega V (modelEmbed ![C, D]) =
      E • modelEmbed ![C, D]) : C = 0 ∧ D = 0 := by
  have hleak := congrArg (fun ψ : Carrier => (ψ 2 2).a) heig
  rw [fullHamiltonian_level_two] at hleak
  have hVD : V * D = 0 := by
    simpa [modelEmbed, InfoGeometry.Algebra.ZornVectorMatrix.smul,
      InfoGeometry.Algebra.ZornVectorMatrix.zero] using hleak
  have hD : D = 0 := (mul_eq_zero.mp hVD).resolve_left hV
  have hread := congrArg modelReadout heig
  change compressedAction Eqp omega V ![C, D] = _ at hread
  rw [compressedAction_vector] at hread
  have hsecond := congrFun hread 1
  simp [hD] at hsecond
  exact ⟨hsecond.resolve_left hV, hD⟩

end InfoGeometry.Physics.NuclearConfigurationGradedReadout
