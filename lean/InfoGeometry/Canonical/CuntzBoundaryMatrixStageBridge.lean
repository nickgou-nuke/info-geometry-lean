/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixRepresentationRefinementBridge
import InfoGeometry.OperatorAlgebra.CantorBernoulliSpatialCylinderStateBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Canonical interface for the concrete boundary matrix-stage morphism

The operator-algebra owners construct the genuine finite-stage `StarAlgHom`.
This file exposes that construction under the canonical generator-level names
used by the matrix-tower contract.
-/

noncomputable section

namespace InfoGeometry.Canonical.CuntzBoundaryMatrixStageBridge

open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixUnitBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzOperatorTreeBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixRepresentationBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixStarRepresentationBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixRepresentationRefinementBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliSpatialCylinderStateBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliSpatialNativeStateBridge

abbrev Stage (n : ℕ) := BitWordMatrixStage n

abbrev BoundaryOperator :=
  InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzCStarRealization.BoundedL2Operator

def boundaryRep (n : ℕ) : Stage n →⋆ₐ[ℂ] BoundaryOperator :=
  bitWordMatrixStarRepresentation n

def correspondingCuntzWord (n : ℕ) (i j : BitWord n) : BoundaryOperator :=
  bitWordUnit n i j

theorem matrixUnit_generator_transport (n : ℕ) (i j : BitWord n) :
    boundaryRep n (Matrix.single i j 1) = correspondingCuntzWord n i j := by
  exact bitWordMatrixStarRepresentation_apply_single n i j

/-! The finite boundary representation is a genuinely noncommutative matrix
readout.  In particular, its definition is controlled by every matrix unit,
not only by the diagonal cylinder projections. -/

theorem boundaryRep_matrix_unit_expansion
    (n : ℕ) (A : Stage n) :
    boundaryRep n A =
      ∑ u : BitWord n, ∑ v : BitWord n,
        A u v • correspondingCuntzWord n u v := by
  rw [Matrix.matrix_eq_sum_single A]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  have hA :
      (∑ i, ∑ j, Matrix.single i j (A i j)) u v = A u v := by
    exact congrArg (fun M => M u v) (Matrix.matrix_eq_sum_single A).symm
  rw [hA]
  rw [show Matrix.single u v (A u v) =
      A u v • Matrix.single u v (1 : ℂ) by
        ext i j
        simp [Matrix.single]]
  rw [map_smul, matrixUnit_generator_transport]

/-- The finite matrix representation sends every diagonal matrix to the
corresponding finite linear combination of Cuntz cylinder projections. -/
theorem boundaryRep_diagonal (n : ℕ) (f : BitWord n → ℂ) :
    boundaryRep n (Matrix.diagonal f) =
      ∑ u : BitWord n, f u • operatorCylinderProjection (List.ofFn u) := by
  rw [show Matrix.diagonal f =
      ∑ u : BitWord n, Matrix.single u u (f u) by
        rw [← Matrix.sum_single_eq_diagonal f]]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro u hu
  rw [show Matrix.single u u (f u) =
      f u • Matrix.single u u (1 : ℂ) by
        ext i j
        simp [Matrix.single]]
  simp only [map_smul, matrixUnit_generator_transport,
    correspondingCuntzWord, bitWordUnit_diag_eq_projection]

/-- The spatial Bernoulli vector state restricted to the represented finite
diagonal matrix stage is the normalized matrix trace. -/
theorem spatialState_boundaryRep_diagonal_eq_matrixTrace
    (n : ℕ) (f : BitWord n → ℂ) :
    spatialState.functional (boundaryRep n (Matrix.diagonal f)) =
      bitWordMatrixTraceFunctional n (Matrix.diagonal f) := by
  calc
    spatialState.functional (boundaryRep n (Matrix.diagonal f)) =
        bitWordMatrixGaugeReadout n (Matrix.diagonal f) := by
      rw [boundaryRep_diagonal]
      change spatialState.functional
          (∑ u : BitWord n,
            f u • operatorCylinderProjection (List.ofFn u)) = _
      rw [map_sum]
      simp_rw [map_smul,
        spatialState_eq_canonicalGaugeState_on_projection]
      simp [bitWordMatrixGaugeReadout, Matrix.diagonal]
    _ = bitWordMatrixTraceFunctional n (Matrix.diagonal f) :=
      bitWordMatrixGaugeReadout_eq_trace n (Matrix.diagonal f)

theorem boundaryRep_bond_compatible (n : ℕ) (A : Stage n) :
    boundaryRep n A = boundaryRep (n + 1) (dyadicMatrixEmbedding n A) := by
  exact bitWordMatrixStarRepresentation_refinement n A

theorem boundaryRep_matrixUnit_bond_compatible (n : ℕ) (i j : BitWord n) :
    correspondingCuntzWord n i j =
      boundaryRep (n + 1)
        (dyadicMatrixEmbedding n (Matrix.single i j 1)) := by
  rw [← matrixUnit_generator_transport n i j]
  exact boundaryRep_bond_compatible n (Matrix.single i j 1)

end InfoGeometry.Canonical.CuntzBoundaryMatrixStageBridge
