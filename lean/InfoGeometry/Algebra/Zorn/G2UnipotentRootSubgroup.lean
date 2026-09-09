import InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
import Mathlib.Tactic

set_option maxHeartbeats 2000000

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace InfoGeometry.Algebra.Zorn.G2Unipotent

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

lemma xor_swap (x0 y0 x1 y1 : Bool) :
    add2 (add2 x0 y0) (add2 x1 y1) = add2 (add2 x0 x1) (add2 y0 y1) := by
  revert x0 y0 x1 y1; decide

def unipotentShort (t : Bool) (X : SplitOctF2) : SplitOctF2 :=
  if t then
    ⟨X.a, X.b, add2 X.x0 X.x1, X.x1, X.x2, X.y0, add2 X.y1 X.y0, X.y2⟩
  else X

@[simp] theorem unipotentShort_false (X : SplitOctF2) :
    unipotentShort false X = X := rfl

theorem unipotentShort_involutive (t : Bool) (X : SplitOctF2) :
    unipotentShort t (unipotentShort t X) = X := by
  cases t
  · rfl
  · rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
    revert a b x0 x1 x2 y0 y1 y2
    native_decide

def unipotentShortEquiv (t : Bool) : SplitOctF2 ≃ SplitOctF2 where
  toFun := unipotentShort t
  invFun := unipotentShort t
  left_inv := unipotentShort_involutive t
  right_inv := unipotentShort_involutive t

theorem unipotentShort_one (t : Bool) : unipotentShort t one = one := by
  cases t <;> rfl

theorem unipotentShort_add (t : Bool) (X Y : SplitOctF2) :
    unipotentShort t (add X Y) = add (unipotentShort t X) (unipotentShort t Y) := by
  cases t
  · rfl
  · rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
    rcases Y with ⟨a',b',x0',x1',x2',y0',y1',y2'⟩
    revert a b x0 x1 x2 y0 y1 y2 a' b' x0' x1' x2' y0' y1' y2'
    native_decide

theorem unipotentShort_mul (t : Bool) (X Y : SplitOctF2) :
    unipotentShort t (mul X Y) = mul (unipotentShort t X) (unipotentShort t Y) := by
  cases t
  · rfl
  · rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
    rcases Y with ⟨a',b',x0',x1',x2',y0',y1',y2'⟩
    revert a b x0 x1 x2 y0 y1 y2 a' b' x0' x1' x2' y0' y1' y2'
    native_decide

def unipotentShortAut (t : Bool) : SplitOctF2Aut where
  val := unipotentShortEquiv t
  property := ⟨unipotentShort_one t, by
    intro X Y
    rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
    rcases Y with ⟨a',b',x0',x1',x2',y0',y1',y2'⟩
    cases t
    · rfl
    · revert a b x0 x1 x2 y0 y1 y2 a' b' x0' x1' x2' y0' y1' y2'
      native_decide, unipotentShort_mul t⟩

theorem unipotentShortAut_order (t : Bool) :
    unipotentShortAut t * unipotentShortAut t = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  intro X
  exact unipotentShort_involutive t X

def unipotentLong (t : Bool) (X : SplitOctF2) : SplitOctF2 :=
  if t then
    ⟨X.a, X.b, X.x0, add2 X.x1 X.x2, X.x2, X.y0, X.y1, add2 X.y2 X.y1⟩
  else X

@[simp] theorem unipotentLong_false (X : SplitOctF2) :
    unipotentLong false X = X := rfl

theorem unipotentLong_involutive (t : Bool) (X : SplitOctF2) :
    unipotentLong t (unipotentLong t X) = X := by
  cases t
  · rfl
  · rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
    revert a b x0 x1 x2 y0 y1 y2
    native_decide

def unipotentLongEquiv (t : Bool) : SplitOctF2 ≃ SplitOctF2 where
  toFun := unipotentLong t
  invFun := unipotentLong t
  left_inv := unipotentLong_involutive t
  right_inv := unipotentLong_involutive t

theorem unipotentLong_one (t : Bool) : unipotentLong t one = one := by
  cases t <;> rfl

theorem unipotentLong_add (t : Bool) (X Y : SplitOctF2) :
    unipotentLong t (add X Y) = add (unipotentLong t X) (unipotentLong t Y) := by
  cases t
  · rfl
  · rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
    rcases Y with ⟨a',b',x0',x1',x2',y0',y1',y2'⟩
    revert a b x0 x1 x2 y0 y1 y2 a' b' x0' x1' x2' y0' y1' y2'
    native_decide

theorem unipotentLong_mul (t : Bool) (X Y : SplitOctF2) :
    unipotentLong t (mul X Y) = mul (unipotentLong t X) (unipotentLong t Y) := by
  cases t
  · rfl
  · rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
    rcases Y with ⟨a',b',x0',x1',x2',y0',y1',y2'⟩
    revert a b x0 x1 x2 y0 y1 y2 a' b' x0' x1' x2' y0' y1' y2'
    native_decide

def unipotentLongAut (t : Bool) : SplitOctF2Aut where
  val := unipotentLongEquiv t
  property := ⟨unipotentLong_one t, by
    intro X Y
    rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
    rcases Y with ⟨a',b',x0',x1',x2',y0',y1',y2'⟩
    cases t
    · rfl
    · revert a b x0 x1 x2 y0 y1 y2 a' b' x0' x1' x2' y0' y1' y2'
      native_decide, unipotentLong_mul t⟩

theorem unipotentLongAut_order (t : Bool) :
    unipotentLongAut t * unipotentLongAut t = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  intro X
  exact unipotentLong_involutive t X

end InfoGeometry.Algebra.Zorn.G2Unipotent
