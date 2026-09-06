import InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

/-! Coordinate audit: the affine eight-coordinate carrier is not the 189-flag variety. -/

namespace InfoGeometry.Algebra.Zorn.G2FlagFiniteGeometry

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

def splitNorm (X : SplitOctF2) : Bool :=
  Bool.xor (X.a && X.b)
    (Bool.xor (X.x0 && X.y0) (Bool.xor (X.x1 && X.y1) (X.x2 && X.y2)))

def IsIsotropic (X : SplitOctF2) : Prop := splitNorm X = false

instance (X : SplitOctF2) : Decidable (IsIsotropic X) := by
  dsimp [IsIsotropic]
  infer_instance

def isotropicPoints : Finset SplitOctF2 := Finset.univ.filter IsIsotropic

def nonzeroIsotropicPoints : Finset SplitOctF2 := isotropicPoints.erase zero

theorem isotropicPoints_card : isotropicPoints.card = 136 := by native_decide

theorem nonzeroIsotropicPoints_card : nonzeroIsotropicPoints.card = 135 := by native_decide

end InfoGeometry.Algebra.Zorn.G2FlagFiniteGeometry
