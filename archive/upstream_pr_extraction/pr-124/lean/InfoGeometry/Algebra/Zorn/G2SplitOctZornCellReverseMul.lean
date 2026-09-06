import InfoGeometry.Algebra.Zorn.G2SplitOctZornCellBridge

namespace InfoGeometry.Algebra.Zorn.G2SplitOctZornCellBridge

open InfoGeometry.Algebra.Zorn.Concrete
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

theorem ofZornCell_mulZ (X Y : ZornCell (ZMod 2)) :
    ofZornCell (ZornCell.mulZ X Y) =
      mul (ofZornCell X) (ofZornCell Y) := by
  rcases X with ⟨r, s, x1, x2, x3, y1, y2, y3⟩
  rcases Y with ⟨r', s', x1', x2', x3', y1', y2', y3'⟩
  apply SplitOctF2.ext
  all_goals
    simp [ofZornCell, ZornCell.mulZ, mul, add2, mul2, dot3, cross0,
      cross1, cross2, zModToBool_add, zModToBool_mul, sub_eq_add_neg,
      Bool.xor_comm, Bool.xor_left_comm]

end InfoGeometry.Algebra.Zorn.G2SplitOctZornCellBridge
