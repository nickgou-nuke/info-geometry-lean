/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Algebra.CuntzComplexStarBinaryGaugeDegreeZero
import InfoGeometry.OperatorAlgebra.CantorBernoulliComplexStarFiniteStageBridge

/-!
# Boundary representation of the gauge-fixed finite matrix core

The degree-zero coefficient of the integer gauge grading is a fixed-point
readout, not a spectral diagonalization.  This owner connects that readout to
the existing concrete boundary representation on every finite matrix stage.
The matrix argument is arbitrary; its full matrix-unit expansion is retained,
including off-diagonal and non-diagonalizable components.
-/

noncomputable section

namespace InfoGeometry.Algebra.CuntzComplexStarBinaryGaugeDegreeZeroRepresentation

open InfoGeometry.Physics.ComplexStarCuntzRedesign
open InfoGeometry.Algebra.CuntzIntegerGrading
open InfoGeometry.Algebra.CuntzComplexStarBinaryGaugeDegreeZero
open InfoGeometry.OperatorAlgebra.CantorBernoulliTensorQuotientPrefixMeasureBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliComplexStarFiniteStageBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzStarRepresentationBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixUnitBridge
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.CuntzBoundaryMatrixStageBridge

abbrev Carrier := ComplexStarCuntzAlg Bool
abbrev BoundaryOperator :=
  InfoGeometry.Canonical.CuntzBoundaryMatrixStageBridge.BoundaryOperator

theorem degreeZero_delta_finiteStageElement_boundaryRep
    (n : ℕ) (A : BitWordMatrixStage n) :
    cantorBernoulliComplexStarLift
        (degreeZero (delta (complexStarFiniteStageElement n A))) =
      boundaryRep n A := by
  rw [degreeZero_delta_finiteStageElement]
  exact complexStarFiniteStageElement_representation n A

end InfoGeometry.Algebra.CuntzComplexStarBinaryGaugeDegreeZeroRepresentation
