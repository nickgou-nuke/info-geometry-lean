/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.OperatorGeometryExamples

/-!
# Kernel axiom audit for matrix projection and Kraus counterexamples

The full matrix carrier is used. The examples distinguish positivity of a
matrix from positivity preservation by a Peirce component, and completeness of
a Kraus family from multiplicativity of its map.
-/

#print axioms InfoGeometry.OperatorAlgebra.OperatorGeometryExamples.projections_not_commute
#print axioms InfoGeometry.OperatorAlgebra.OperatorGeometryExamples.Q_posSemidef
#print axioms InfoGeometry.OperatorAlgebra.OperatorGeometryExamples.oddPart_Q_not_posSemidef
#print axioms InfoGeometry.OperatorAlgebra.OperatorGeometryExamples.V_complete
#print axioms InfoGeometry.OperatorAlgebra.OperatorGeometryExamples.krausMap_not_multiplicative
#print axioms InfoGeometry.OperatorAlgebra.OperatorGeometryExamples.single_isometric_kraus_multiplicative
