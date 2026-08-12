import InfoGeometry.Canonical.ThreeColorOperatorCrossCommutator

/-!
# A theorem-honest third-order scalar readout

This file records the finite commutative-coefficient identity behind the
scalar triple product.  It does **not** identify this readout with a Chentsov
tensor, Cartan torsion, or the raw Zorn associator.  For noncommutative
coefficients the displayed cyclic/alternating identities are intentionally
not asserted: coefficient order is part of the operator-valued product.
-/

namespace InfoGeometry.Canonical

section CommutativeCoefficients

variable {C : Type*} [CommRing C]

/-- The scalar third-order Levi--Civita readout of three colour vectors. -/
def operatorTripleProduct (U V W : OperatorVector C) : C :=
  operatorDot (operatorCross U V) W

/-- Swapping the first two entries reverses the scalar triple-product sign. -/
theorem operatorTripleProduct_swap_left
    (U V W : OperatorVector C) :
    operatorTripleProduct U V W = -operatorTripleProduct V U W := by
  dsimp [operatorTripleProduct, operatorDot, operatorCross,
    InfoGeometry.Physics.NCG.NCZornElement.zornDot,
    InfoGeometry.Physics.NCG.NCZornElement.zornCross]
  ring

/-- Cyclic permutation preserves the commutative scalar triple product. -/
theorem operatorTripleProduct_cyclic
    (U V W : OperatorVector C) :
    operatorTripleProduct U V W = operatorTripleProduct V W U := by
  dsimp [operatorTripleProduct, operatorDot, operatorCross,
    InfoGeometry.Physics.NCG.NCZornElement.zornDot,
    InfoGeometry.Physics.NCG.NCZornElement.zornCross]
  ring

end CommutativeCoefficients

end InfoGeometry.Canonical
