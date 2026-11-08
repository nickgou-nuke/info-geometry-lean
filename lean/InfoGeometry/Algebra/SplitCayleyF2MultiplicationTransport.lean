import InfoGeometry.Algebra.SplitCayleyF2CarrierAlignment
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2SplitOctZornCellReverseMul

namespace InfoGeometry.Algebra.SplitCayleyF2

open InfoGeometry.Algebra.Zorn.G2SplitOctZornCellBridge
open InfoGeometry.Algebra.Zorn.Concrete
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

theorem cayleyToSplitOctF2_mul (x y : Cayley) :
    cayleyToSplitOctF2 (x * y) =
      InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.mul
        (cayleyToSplitOctF2 x) (cayleyToSplitOctF2 y) := by
  have h := congrArg
    InfoGeometry.Algebra.Zorn.G2SplitOctZornCellBridge.ofZornCell
    (toZornCell_mul x y)
  calc
    cayleyToSplitOctF2 (x * y) =
        InfoGeometry.Algebra.Zorn.G2SplitOctZornCellBridge.ofZornCell
          (ZornCell.mulZ (toZornCell x) (toZornCell y)) := by
          simpa [cayleyToSplitOctF2, ofZornCell_toZornCell] using h
    _ = InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.mul
        (cayleyToSplitOctF2 x) (cayleyToSplitOctF2 y) := by
          simpa [cayleyToSplitOctF2, ofZornCell_toZornCell] using
            ofZornCell_mulZ (toZornCell x) (toZornCell y)

end InfoGeometry.Algebra.SplitCayleyF2
