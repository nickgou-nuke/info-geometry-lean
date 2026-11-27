/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.CuntzMatrixUnitRepresentation

/-!
# Counterexample audit for the raw Cuntz isometry block

The exact square identity and its non-involution consequence are audited in
the same abstract semiring presentation as their owner declarations.
-/

namespace InfoGeometry.Algebra.Cuntz.CuntzMatrixUnitRepresentationAudit

open InfoGeometry.Algebra.Cuntz

#print axioms AlgebraicCuntzNPresentation.raw_isometry_block_square
#print axioms AlgebraicCuntzNPresentation.matrixUnit_zero_zero_ne_one
#print axioms AlgebraicCuntzNPresentation.raw_isometry_block_not_involution

end InfoGeometry.Algebra.Cuntz.CuntzMatrixUnitRepresentationAudit
