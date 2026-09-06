import InfoGeometry.Algebra.Zorn.G2NativeFlagOrbitClosure
import InfoGeometry.Algebra.Zorn.G2NativeFlagIntrinsicEquiv

/-!
# Quotient to intrinsic-flag assembly

This owner records the exact final transport once the native flag
stabilizer has been identified with the concrete unipotent subgroup.  The
stabilizer equality remains an explicit hypothesis; no quotient cardinality
or representative-table assertion is used here.
-/

namespace InfoGeometry.Algebra.Zorn.G2QuotientIntrinsicFlagAssembly

open InfoGeometry.Algebra.Zorn.G2NativeFlagIntrinsicEquiv
open InfoGeometry.Algebra.Zorn.G2IntrinsicFlagAction
open InfoGeometry.Algebra.Zorn.G2NativeFlagOrbitClosure
open InfoGeometry.Algebra.Zorn.G2NativeCandidateFiberAction
open InfoGeometry.Algebra.Zorn.G2NativeFullFlagCarrier
open InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

noncomputable def quotientUnipotentIntrinsicFlagEquiv_of_stabilizer_eq
    (hstab :
      MulAction.stabilizer SplitOctF2Aut nativeBaseFlag =
        unipotentSubgroup) :
    SplitOctF2Aut ⧸ unipotentSubgroup ≃ G2IntrinsicFlagAction.IntrinsicFlag :=
  (nativeFlag_quotientUnipotentEquiv_of_stabilizer_eq hstab).symm.trans
    nativeFlagIntrinsicEquiv

end InfoGeometry.Algebra.Zorn.G2QuotientIntrinsicFlagAssembly
