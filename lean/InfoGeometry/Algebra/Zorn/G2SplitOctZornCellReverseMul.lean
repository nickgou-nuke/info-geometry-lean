import InfoGeometry.Algebra.Zorn.G2SplitOctZornCellBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Algebra.Zorn.G2SplitOctZornCellBridge

open InfoGeometry.Algebra.Zorn.Concrete
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

theorem ofZornCell_mulZ (X Y : ZornCell (ZMod 2)) :
    ofZornCell (ZornCell.mulZ X Y) =
      mul (ofZornCell X) (ofZornCell Y) := by
  have h := toZornCell_mul (ofZornCell X) (ofZornCell Y)
  rw [toZornCell_ofZornCell, toZornCell_ofZornCell] at h
  rw [← h, ofZornCell_toZornCell]

end InfoGeometry.Algebra.Zorn.G2SplitOctZornCellBridge
