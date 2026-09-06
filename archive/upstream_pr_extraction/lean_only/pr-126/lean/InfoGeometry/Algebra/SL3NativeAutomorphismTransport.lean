import InfoGeometry.Algebra.SL3DualActionF2
import InfoGeometry.Algebra.SplitCayleyF2AutomorphismTransport

namespace InfoGeometry.Algebra.SplitCayleyF2

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

noncomputable def cyclicNativeAutomorphism : SplitOctF2Aut :=
  cyclicAddMulAutomorphism.toSplitOctF2Aut

noncomputable def shearNativeAutomorphism : SplitOctF2Aut :=
  shearAddMulAutomorphism.toSplitOctF2Aut

theorem cyclicNativeAutomorphism_map_mul (x y : SplitOctF2) :
    cyclicNativeAutomorphism.1 (InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.mul x y) =
      InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.mul
        (cyclicNativeAutomorphism.1 x) (cyclicNativeAutomorphism.1 y) := by
  exact cyclicAddMulAutomorphism.toSplitOctF2Equiv_mul x y

theorem shearNativeAutomorphism_map_mul (x y : SplitOctF2) :
    shearNativeAutomorphism.1 (InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.mul x y) =
      InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.mul
        (shearNativeAutomorphism.1 x) (shearNativeAutomorphism.1 y) := by
  exact shearAddMulAutomorphism.toSplitOctF2Equiv_mul x y

theorem cyclicNativeAutomorphism_map_add (x y : SplitOctF2) :
    cyclicNativeAutomorphism.1 (InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.add x y) =
      InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.add
        (cyclicNativeAutomorphism.1 x) (cyclicNativeAutomorphism.1 y) := by
  exact cyclicAddMulAutomorphism.toSplitOctF2Equiv_add x y

theorem shearNativeAutomorphism_map_add (x y : SplitOctF2) :
    shearNativeAutomorphism.1 (InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.add x y) =
      InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.add
        (shearNativeAutomorphism.1 x) (shearNativeAutomorphism.1 y) := by
  exact shearAddMulAutomorphism.toSplitOctF2Equiv_add x y

theorem cyclicNativeAutomorphism_map_one :
    cyclicNativeAutomorphism.1
        InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.one =
      InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.one := by
  exact cyclicAddMulAutomorphism.toSplitOctF2Equiv_one

theorem shearNativeAutomorphism_map_one :
    shearNativeAutomorphism.1
        InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.one =
      InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.one := by
  exact shearAddMulAutomorphism.toSplitOctF2Equiv_one

theorem cyclicNativeAutomorphism_cayley_readback (x : SplitOctF2) :
    cayleySplitOctF2Equiv.symm (cyclicNativeAutomorphism.1 x) =
      cyclicAction (cayleySplitOctF2Equiv.symm x) := by
  exact AddMulAutomorphism.toSplitOctF2Equiv_cayley_readback
    cyclicAddMulAutomorphism x

theorem shearNativeAutomorphism_cayley_readback (x : SplitOctF2) :
    cayleySplitOctF2Equiv.symm (shearNativeAutomorphism.1 x) =
      shearAction (cayleySplitOctF2Equiv.symm x) := by
  exact AddMulAutomorphism.toSplitOctF2Equiv_cayley_readback
    shearAddMulAutomorphism x

theorem cyclicNativeAutomorphism_cube (x : SplitOctF2) :
    cyclicNativeAutomorphism.1
        (cyclicNativeAutomorphism.1 (cyclicNativeAutomorphism.1 x)) = x := by
  apply cayleySplitOctF2Equiv.symm.injective
  rw [cyclicNativeAutomorphism_cayley_readback,
    cyclicNativeAutomorphism_cayley_readback,
    cyclicNativeAutomorphism_cayley_readback]
  exact cyclicAction_three _

theorem shearNativeAutomorphism_square (x : SplitOctF2) :
    shearNativeAutomorphism.1 (shearNativeAutomorphism.1 x) = x := by
  apply cayleySplitOctF2Equiv.symm.injective
  rw [shearNativeAutomorphism_cayley_readback,
    shearNativeAutomorphism_cayley_readback]
  exact shearAction_square _

end InfoGeometry.Algebra.SplitCayleyF2
