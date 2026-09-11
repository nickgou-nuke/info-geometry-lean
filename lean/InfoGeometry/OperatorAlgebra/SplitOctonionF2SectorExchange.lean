import InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Sector exchange on the finite split-octonion carrier

The exchange is defined on the actual finite `SplitOctF2` carrier and then
packaged as an element of `SplitOctF2Aut`.  This is deliberately separate
from the non-associative Zorn carrier and from any semidirect product.
-/

namespace InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

def sectorExchangeF2 : SplitOctF2 ≃ SplitOctF2 where
  toFun X :=
    { a := X.b, b := X.a,
      x0 := X.y0, x1 := X.y1, x2 := X.y2,
      y0 := X.x0, y1 := X.x1, y2 := X.x2 }
  invFun X :=
    { a := X.b, b := X.a,
      x0 := X.y0, x1 := X.y1, x2 := X.y2,
      y0 := X.x0, y1 := X.x1, y2 := X.x2 }
  left_inv X := by cases X; rfl
  right_inv X := by cases X; rfl

theorem sectorExchangeF2_add (X Y : SplitOctF2) :
    sectorExchangeF2 (add X Y) = add (sectorExchangeF2 X) (sectorExchangeF2 Y) := by
  native_decide +revert

theorem sectorExchangeF2_mul (X Y : SplitOctF2) :
    sectorExchangeF2 (mul X Y) = mul (sectorExchangeF2 X) (sectorExchangeF2 Y) := by
  native_decide +revert

def sectorExchangeF2Aut : SplitOctF2Aut :=
  ⟨sectorExchangeF2,
    ⟨by native_decide +revert, sectorExchangeF2_add, sectorExchangeF2_mul⟩⟩

theorem sectorExchangeF2Aut_apply (X : SplitOctF2) :
    sectorExchangeF2Aut.1 X = sectorExchangeF2 X := rfl

@[simp] theorem sectorExchangeF2_ePlus :
    sectorExchangeF2 ePlus = eMinus := rfl

@[simp] theorem sectorExchangeF2_eMinus :
    sectorExchangeF2 eMinus = ePlus := rfl

@[simp] theorem sectorExchangeF2_up0 :
    sectorExchangeF2 up0 = down0 := rfl

@[simp] theorem sectorExchangeF2_up1 :
    sectorExchangeF2 up1 = down1 := rfl

@[simp] theorem sectorExchangeF2_up2 :
    sectorExchangeF2 up2 = down2 := rfl

@[simp] theorem sectorExchangeF2_down0 :
    sectorExchangeF2 down0 = up0 := rfl

@[simp] theorem sectorExchangeF2_down1 :
    sectorExchangeF2 down1 = up1 := rfl

@[simp] theorem sectorExchangeF2_down2 :
    sectorExchangeF2 down2 = up2 := rfl

theorem sectorExchangeF2_preserves_idempotent (X : SplitOctF2)
    (hX : mul X X = X) :
    mul (sectorExchangeF2 X) (sectorExchangeF2 X) = sectorExchangeF2 X := by
  rw [← sectorExchangeF2_mul, hX]

theorem sectorExchangeF2_peirce_frame_swap :
    (sectorExchangeF2 ePlus, sectorExchangeF2 eMinus) = (eMinus, ePlus) := by
  rw [sectorExchangeF2_ePlus, sectorExchangeF2_eMinus]

theorem sectorExchangeF2Aut_sq :
    sectorExchangeF2Aut * sectorExchangeF2Aut = (1 : SplitOctF2Aut) := by
  apply Subtype.ext
  apply Equiv.ext
  intro X
  cases X
  rfl

end InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
