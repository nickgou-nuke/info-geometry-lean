import InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier

namespace InfoGeometry.Algebra.Zorn.G2TwoCarrierCoordinateLemmas

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier

@[simp] theorem carrierToVec_zero (X : SplitOctF2) :
    carrierToVec X 0 = bitToF2 X.a := by
  rfl

@[simp] theorem carrierToVec_one (X : SplitOctF2) :
    carrierToVec X 1 = bitToF2 X.b := by
  rfl

@[simp] theorem carrierToVec_x0 (X : SplitOctF2) :
    carrierToVec X 2 = bitToF2 X.x0 := by
  rfl

@[simp] theorem carrierToVec_x1 (X : SplitOctF2) :
    carrierToVec X 3 = bitToF2 X.x1 := by
  rfl

@[simp] theorem carrierToVec_x2 (X : SplitOctF2) :
    carrierToVec X 4 = bitToF2 X.x2 := by
  rfl

@[simp] theorem carrierToVec_y0 (X : SplitOctF2) :
    carrierToVec X 5 = bitToF2 X.y0 := by
  rfl

@[simp] theorem carrierToVec_y1 (X : SplitOctF2) :
    carrierToVec X 6 = bitToF2 X.y1 := by
  rfl

@[simp] theorem carrierToVec_y2 (X : SplitOctF2) :
    carrierToVec X 7 = bitToF2 X.y2 := by
  rfl

end InfoGeometry.Algebra.Zorn.G2TwoCarrierCoordinateLemmas
