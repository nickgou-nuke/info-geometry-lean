/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.NuclearComplementaryResolvent
import InfoGeometry.Physics.NuclearConfigurationGradedReadout

/-!
# Resolvent correction to the existing nuclear configuration readout

The projector and full Hamiltonian are exactly those already used in the
five-grade CAR--phonon model. The reduced matrix is its existing QPNM block
plus the eliminated-space self-energy. A supplied supported right inverse makes
its spectral equation equivalent to the equation on reconstructed graph states.
This does not reconstruct every full eigenvector. On the unrestricted algebraic
carrier, `NuclearAlgebraicResolventObstruction` excludes a left complementary
inverse at nonzero coupling; a two-sided spectral reduction therefore requires
a different compatible realization with appropriate domain restrictions.
-/

noncomputable section

namespace InfoGeometry.Physics.NuclearFeshbachConfigurationBridge

open Matrix
open InfoGeometry.Physics.NuclearFeshbachReduction
open InfoGeometry.Physics.NuclearFiveGradeCommonCarrierRepresentation
open InfoGeometry.Physics.NuclearFiveGradeSolovievCommonCompression
open InfoGeometry.Physics.NuclearConfigurationOperatorLift
open InfoGeometry.Physics.NuclearConfigurationGradedReadout
open InfoGeometry.Physics.SolovievQPNMEigenproblem

theorem modelMatrix_add (A B : Operator) :
    modelMatrix (A + B) = modelMatrix A + modelMatrix B := by
  simp [modelMatrix, LinearMap.add_comp, LinearMap.comp_add]

/-- The same exact readout eliminates redundant outer model projectors. -/
theorem modelMatrix_projection_sandwich (T : Operator) :
    modelMatrix (modelProjection * T * modelProjection) = modelMatrix T := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  change (modelMatrix (modelProjection * T * modelProjection)).mulVec v =
    (modelMatrix T).mulVec v
  simp only [modelMatrix_mulVec, Module.End.mul_apply, modelProjection,
    LinearMap.comp_apply, modelReadout_modelEmbed]

/-- The effective operator really takes values in the selected model image. -/
theorem effectiveHamiltonian_on_model (H R : Operator) (v : ModelVector) :
    effectiveHamiltonian modelProjection H R (modelEmbed v) =
      modelEmbed ((modelMatrix (effectiveHamiltonian modelProjection H R)).mulVec v) := by
  have h := LinearMap.congr_fun
    (effectiveHamiltonian_supported modelProjection H R modelProjection_idempotent).1
    (modelEmbed v)
  rw [modelMatrix_mulVec]
  exact h.symm

/-- Exact self-energy correction to the already proved QPNM compression. -/
theorem effective_modelMatrix (Eqp omega coupling : ℝ) (R : Operator) :
    modelMatrix (effectiveHamiltonian modelProjection
      (fullHamiltonian Eqp omega coupling) R) =
      qpnmMatrix Eqp omega coupling +
        modelMatrix (fullHamiltonian Eqp omega coupling * R *
          fullHamiltonian Eqp omega coupling) := by
  rw [effectiveHamiltonian, modelMatrix_add,
    ← cornerLift_qpnm_eq_projected, modelMatrix_cornerLift]
  congr 1

/-- The corrected matrix controls the equation on reconstructed graph states
at the supplied energy. Only a supported right inverse is assumed; completeness
of this graph among full eigenvectors is not asserted. -/
theorem full_eigen_equation_iff_corrected_matrix
    (Eqp omega coupling E : ℝ) (R : Operator)
    (hQR : (1 - modelProjection) * R = R)
    (hDR : denominator modelProjection (fullHamiltonian Eqp omega coupling) E * R =
      1 - modelProjection) (v : ModelVector) :
    fullHamiltonian Eqp omega coupling
        (waveOperator modelProjection (fullHamiltonian Eqp omega coupling) R (modelEmbed v)) =
      E • waveOperator modelProjection (fullHamiltonian Eqp omega coupling) R (modelEmbed v) ↔
    (qpnmMatrix Eqp omega coupling +
      modelMatrix (fullHamiltonian Eqp omega coupling * R *
        fullHamiltonian Eqp omega coupling)).mulVec v = E • v := by
  rw [eigen_equation_iff modelProjection (fullHamiltonian Eqp omega coupling) R E
    hQR hDR (modelEmbed v) (modelProjection_modelEmbed v),
    effectiveHamiltonian_on_model, effective_modelMatrix]
  constructor
  · intro h
    simpa only [map_smul, modelReadout_modelEmbed] using congrArg modelReadout h
  · intro h
    rw [h, map_smul]

end InfoGeometry.Physics.NuclearFeshbachConfigurationBridge
