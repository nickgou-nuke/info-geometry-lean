import InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzOperatorTreeBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Matrix-unit action on cylinder projections

The matrix-unit action is exposed directly from word cancellation.  This
owner deliberately stops at the operator identity; coefficient recovery is a
separate faithfulness theorem.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.CantorBernoulliMatrixUnitAction

open InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzOperatorTreeBridge
open InfoGeometry.Canonical.CantorBernoulliL2OperatorTransport

theorem operatorMatrixUnit_apply_cylinderProjection
    (u v : List Bool) (f : L2Boundary) :
    operatorMatrixUnit u v (operatorCylinderProjection v f) =
      operatorWord u (operatorWordDag v f) := by
  unfold operatorMatrixUnit operatorCylinderProjection
  change operatorWord u
      (operatorWordDag v (operatorWord v (operatorWordDag v f))) = _
  have h := ContinuousLinearMap.ext_iff.mp
    (operatorWordDag_comp_operatorWord v) (operatorWordDag v f)
  simpa using congrArg (operatorWord u) h

end InfoGeometry.OperatorAlgebra.CantorBernoulliMatrixUnitAction

end noncomputable section
