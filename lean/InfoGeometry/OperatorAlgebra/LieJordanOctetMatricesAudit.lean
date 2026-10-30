/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.LieJordanOctetMatrices

/-!
# Signed-sandwich positivity counterexample audit

Audit the explicit non-positive signed action and its correctly scoped
positive adjoint-paired cross-transport replacement.
-/

namespace InfoGeometry.OperatorAlgebra.LieJordanOctetMatricesAudit

#print axioms InfoGeometry.OperatorAlgebra.LieJordanOctetMatrices.jump_square_zero
#print axioms InfoGeometry.OperatorAlgebra.LieJordanOctetMatrices.jump_noncommutes_adjoint
#print axioms InfoGeometry.OperatorAlgebra.LieJordanOctetMatrices.oriented_adjoint_not_positive
#print axioms InfoGeometry.OperatorAlgebra.LieJordanOctetMatrices.matrix_trace_oriented
#print axioms InfoGeometry.OperatorAlgebra.LieJordanBoundaryMatrices.crossTransport_posSemidef
#print axioms InfoGeometry.OperatorAlgebra.LieJordanBoundaryMatrices.adjoint_cross_trace_preserving

end InfoGeometry.OperatorAlgebra.LieJordanOctetMatricesAudit
