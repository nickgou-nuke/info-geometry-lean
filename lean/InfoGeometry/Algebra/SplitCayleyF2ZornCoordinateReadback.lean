import InfoGeometry.Algebra.SplitCayleyF2CarrierAlignment
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Algebra.SplitCayleyF2

open InfoGeometry.Algebra.Zorn.G2SplitOctZornCellBridge

theorem nativeZornCell_cayley_readback (x : Cayley) :
    InfoGeometry.Algebra.Zorn.G2SplitOctZornCellBridge.toZornCell
        (cayleyToSplitOctF2 x) =
      InfoGeometry.Algebra.SplitCayleyF2.toZornCell x := by
  rcases x with ⟨a, u, v, b⟩
  simp only [cayleyToSplitOctF2, toZornCell,
    InfoGeometry.Algebra.Zorn.G2SplitOctZornCellBridge.toZornCell,
    InfoGeometry.Algebra.Zorn.G2SplitOctZornCellBridge.ofZornCell,
    InfoGeometry.Algebra.Zorn.G2SplitOctZornCellBridge.boolToZMod,
    InfoGeometry.Algebra.Zorn.G2SplitOctZornCellBridge.zModToBool]
  congr 1
  all_goals
    change boolToZMod (zModToBool _) = _
    exact boolToZMod_zModToBool _

end InfoGeometry.Algebra.SplitCayleyF2
