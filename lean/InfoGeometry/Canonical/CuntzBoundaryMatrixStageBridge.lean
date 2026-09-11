import InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixRepresentationRefinementBridge
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
open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixRepresentationBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixStarRepresentationBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixRepresentationRefinementBridge

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
