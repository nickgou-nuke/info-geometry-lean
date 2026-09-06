import InfoGeometry.Algebra.SplitCayleyF2
import InfoGeometry.Algebra.Zorn.Concrete
import InfoGeometry.Algebra.Zorn.G2SplitOctZornCellBridge

namespace InfoGeometry.Algebra.SplitCayleyF2

open InfoGeometry.Algebra.Zorn.Concrete
open InfoGeometry.Algebra.Zorn.G2SplitOctZornCellBridge

def toZornCell (x : Cayley) : ZornCell Scalar where
  r := x.α
  s := x.β
  x1 := x.u 0
  x2 := x.u 1
  x3 := x.u 2
  y1 := x.v 0
  y2 := x.v 1
  y3 := x.v 2

def ofZornCell (x : ZornCell Scalar) : Cayley where
  α := x.r
  u := ![x.x1, x.x2, x.x3]
  v := ![x.y1, x.y2, x.y3]
  β := x.s

def cayleyToSplitOctF2 (x : Cayley) :
    InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.SplitOctF2 :=
  InfoGeometry.Algebra.Zorn.G2SplitOctZornCellBridge.ofZornCell
    (toZornCell x)

def splitOctF2ToCayley
    (x : InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.SplitOctF2) : Cayley :=
  ofZornCell
    (InfoGeometry.Algebra.Zorn.G2SplitOctZornCellBridge.toZornCell x)

noncomputable def cayleyZornCellEquiv : Cayley ≃ ZornCell Scalar where
  toFun := toZornCell
  invFun := ofZornCell
  left_inv := by
    intro x
    cases x
    apply Cayley.ext
    · rfl
    · funext i
      fin_cases i <;> rfl
    · funext i
      fin_cases i <;> rfl
    · rfl
  right_inv := by
    intro x
    cases x
    rfl

noncomputable def cayleySplitOctF2Equiv : Cayley ≃
    InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.SplitOctF2 where
  toFun := cayleyToSplitOctF2
  invFun := splitOctF2ToCayley
  left_inv := by
    intro x
    apply cayleyZornCellEquiv.injective
    simp [cayleyToSplitOctF2, splitOctF2ToCayley, cayleyZornCellEquiv,
      toZornCell, ofZornCell,
      InfoGeometry.Algebra.Zorn.G2SplitOctZornCellBridge.toZornCell,
      InfoGeometry.Algebra.Zorn.G2SplitOctZornCellBridge.ofZornCell,
      InfoGeometry.Algebra.Zorn.G2SplitOctZornCellBridge.boolToZMod_zModToBool]
  right_inv := by
    intro x
    exact InfoGeometry.Algebra.Zorn.G2SplitOctZornCellBridge.ofZornCell_toZornCell x

theorem cayley_card_eq_splitOctF2_card :
    Fintype.card Cayley =
      Fintype.card InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.SplitOctF2 :=
  Fintype.card_congr cayleySplitOctF2Equiv

theorem toZornCell_mul (x y : Cayley) :
    toZornCell (x * y) = ZornCell.mulZ (toZornCell x) (toZornCell y) := by
  cases x with
  | mk xa xu xv xb =>
    cases y with
    | mk ya yu yv yb =>
      congr 1

theorem toZornCell_add (x y : Cayley) :
    toZornCell (add x y) = ZornCell.addZ (toZornCell x) (toZornCell y) := by
  cases x with
  | mk xa xu xv xb =>
    cases y with
    | mk ya yu yv yb =>
      congr 1

theorem toZornCell_norm (x : Cayley) :
    ZornCell.detZ (toZornCell x) = norm x := by
  rfl

theorem cayleySplitOctF2Equiv_one :
    cayleySplitOctF2Equiv (one : Cayley) =
      InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.one := by
  decide

theorem zModToBool_add (a b : Scalar) :
    zModToBool (a + b) = (zModToBool a ^^ zModToBool b) := by
  fin_cases a <;> fin_cases b <;> rfl

theorem cayleySplitOctF2Equiv_add (x y : Cayley) :
    cayleyToSplitOctF2 (add x y) =
      InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.add
        (cayleyToSplitOctF2 x) (cayleyToSplitOctF2 y) := by
  cases x with
  | mk xa xu xv xb =>
    cases y with
    | mk ya yu yv yb =>
      simp [cayleyToSplitOctF2, add, toZornCell,
        InfoGeometry.Algebra.Zorn.G2SplitOctZornCellBridge.ofZornCell,
        InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.add,
        InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.add2]
      exact ⟨zModToBool_add _ _, zModToBool_add _ _, zModToBool_add _ _,
        zModToBool_add _ _, zModToBool_add _ _, zModToBool_add _ _,
        zModToBool_add _ _, zModToBool_add _ _⟩

theorem cayleySplitOctF2Equiv_mul (x y : Cayley) :
    cayleyToSplitOctF2 (x * y) =
      InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.mul
        (cayleyToSplitOctF2 x) (cayleyToSplitOctF2 y) := by
  dsimp [cayleyToSplitOctF2]
  rw [toZornCell_mul]
  have h := (InfoGeometry.Algebra.Zorn.G2SplitOctZornCellBridge.toZornCell_mul
    (cayleyToSplitOctF2 x) (cayleyToSplitOctF2 y)).symm
  simp only [cayleyToSplitOctF2,
    InfoGeometry.Algebra.Zorn.G2SplitOctZornCellBridge.toZornCell_ofZornCell] at h
  rw [h]
  exact InfoGeometry.Algebra.Zorn.G2SplitOctZornCellBridge.ofZornCell_toZornCell _

end InfoGeometry.Algebra.SplitCayleyF2
