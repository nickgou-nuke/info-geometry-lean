import InfoGeometry.Algebra.SplitCayleyF2ZornCoordinateReadback
import InfoGeometry.Algebra.Zorn.G2SplitOctZornCellBridge

namespace InfoGeometry.Algebra.SplitCayleyF2

open InfoGeometry.Algebra.Zorn.G2FiniteIsotropicPoints
open InfoGeometry.Algebra.Zorn.G2SplitOctZornCellBridge

theorem cayley_norm_bool_readback (x : Cayley) :
    zModToBool (norm x) = zornNorm (cayleyToSplitOctF2 x) := by
  have h : norm x =
      boolToZMod (zornNorm (cayleyToSplitOctF2 x)) := by
    rw [← detZ_toZornCell (cayleyToSplitOctF2 x)]
    rw [← InfoGeometry.Algebra.SplitCayleyF2.toZornCell_norm x]
    congr 1
    exact (nativeZornCell_cayley_readback x).symm
  rw [← zModToBool_boolToZMod (zornNorm (cayleyToSplitOctF2 x))]
  exact congrArg zModToBool h

end InfoGeometry.Algebra.SplitCayleyF2
