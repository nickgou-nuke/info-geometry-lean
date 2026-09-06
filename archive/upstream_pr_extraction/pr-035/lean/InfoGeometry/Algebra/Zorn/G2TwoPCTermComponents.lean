import InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup

namespace InfoGeometry.Algebra.Zorn.G2TwoPCTermComponents

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup

lemma pcTermFun_a (i : Fin 6) (b : Bool) (X : SplitOctF2) :
    (pcTermFun i b X).a = if b then (pcTermFun i true X).a else X.a := by
  cases b <;> fin_cases i <;> rfl

lemma pcTermFun_b (i : Fin 6) (b : Bool) (X : SplitOctF2) :
    (pcTermFun i b X).b = if b then (pcTermFun i true X).b else X.b := by
  cases b <;> fin_cases i <;> rfl

lemma pcTermFun_x0 (i : Fin 6) (b : Bool) (X : SplitOctF2) :
    (pcTermFun i b X).x0 = if b then (pcTermFun i true X).x0 else X.x0 := by
  cases b <;> fin_cases i <;> rfl

lemma pcTermFun_x1 (i : Fin 6) (b : Bool) (X : SplitOctF2) :
    (pcTermFun i b X).x1 = if b then (pcTermFun i true X).x1 else X.x1 := by
  cases b <;> fin_cases i <;> rfl

lemma pcTermFun_x2 (i : Fin 6) (b : Bool) (X : SplitOctF2) :
    (pcTermFun i b X).x2 = if b then (pcTermFun i true X).x2 else X.x2 := by
  cases b <;> fin_cases i <;> rfl

lemma pcTermFun_y0 (i : Fin 6) (b : Bool) (X : SplitOctF2) :
    (pcTermFun i b X).y0 = if b then (pcTermFun i true X).y0 else X.y0 := by
  cases b <;> fin_cases i <;> rfl

lemma pcTermFun_y1 (i : Fin 6) (b : Bool) (X : SplitOctF2) :
    (pcTermFun i b X).y1 = if b then (pcTermFun i true X).y1 else X.y1 := by
  cases b <;> fin_cases i <;> rfl

lemma pcTermFun_y2 (i : Fin 6) (b : Bool) (X : SplitOctF2) :
    (pcTermFun i b X).y2 = if b then (pcTermFun i true X).y2 else X.y2 := by
  cases b <;> fin_cases i <;> rfl

end InfoGeometry.Algebra.Zorn.G2TwoPCTermComponents
