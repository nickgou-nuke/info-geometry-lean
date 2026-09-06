import InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace InfoGeometry.Algebra.Zorn.G2Unipotent

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

lemma xor_swap (x0 y0 x1 y1 : Bool) :
    add2 (add2 x0 y0) (add2 x1 y1) = add2 (add2 x0 x1) (add2 y0 y1) := by
  revert x0 y0 x1 y1; decide

/-!
=============================================================================
PART 1: Short Simple Root Unipotent Generator x_α(t)
=============================================================================
-/

/-- Unipotent root action for simple short root: shifts x0 by x1 and y1 by y0. -/
def unipotentShort (t : Bool) (X : SplitOctF2) : SplitOctF2 :=
  if t then
    ⟨X.a, X.b, add2 X.x0 X.x1, X.x1, X.x2, X.y0, add2 X.y1 X.y0, X.y2⟩
  else
    X

@[simp]
theorem unipotentShort_false (X : SplitOctF2) :
    unipotentShort false X = X := rfl

theorem unipotentShort_involutive (t : Bool) (X : SplitOctF2) :
    unipotentShort t (unipotentShort t X) = X := by
  cases t <;> cases X
  · rfl
  · dsimp [unipotentShort, add2]
    simp

def unipotentShortEquiv (t : Bool) : SplitOctF2 ≃ SplitOctF2 where
  toFun := unipotentShort t
  invFun := unipotentShort t
  left_inv := unipotentShort_involutive t
  right_inv := unipotentShort_involutive t

theorem unipotentShort_one (t : Bool) :
    unipotentShort t one = one := by
  cases t <;> rfl

theorem unipotentShort_add (t : Bool) (X Y : SplitOctF2) :
    unipotentShort t (add X Y) = add (unipotentShort t X) (unipotentShort t Y) := by
  cases t
  · rfl
  · rcases X with ⟨a1, b1, x01, x11, x21, y01, y11, y21⟩
    rcases Y with ⟨a2, b2, x02, x12, x22, y02, y12, y22⟩
    ext
    · rfl
    · rfl
    · dsimp [unipotentShort, add]
      exact xor_swap x01 x02 x11 x12
    · rfl
    · rfl
    · rfl
    · dsimp [unipotentShort, add]
      exact xor_swap y11 y12 y01 y02
    · rfl

theorem unipotentShort_mul (t : Bool) (X Y : SplitOctF2) :
    unipotentShort t (mul X Y) = mul (unipotentShort t X) (unipotentShort t Y) := by
  cases t
  · rfl
  · rcases X with ⟨a1, b1, x01, x11, x21, y01, y11, y21⟩
    rcases Y with ⟨a2, b2, x02, x12, x22, y02, y12, y22⟩
    ext <;>
      (try rfl) <;>
      (try {
        dsimp [unipotentShort, mul, add2, mul2, dot3, cross0, cross1, cross2]
        revert a1 a2 b1 b2 x01 x11 x21 x02 x12 x22 y01 y11 y21 y02 y12 y22
        decide
      })

/-- 🏆 THEOREM: The short root unipotent action is a genuine SplitOctF2 automorphism! -/
def unipotentShortAut (t : Bool) : SplitOctF2Aut where
  val := unipotentShortEquiv t
  property := ⟨unipotentShort_one t, unipotentShort_add t, unipotentShort_mul t⟩

/-- 🏆 THEOREM: Short root unipotent generator has order 2. -/
theorem unipotentShortAut_order (t : Bool) :
    unipotentShortAut t * unipotentShortAut t = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  intro X
  exact unipotentShort_involutive t X

/-!
=============================================================================
PART 2: Long Simple Root Unipotent Generator x_β(t)
=============================================================================
-/

/-- Unipotent root action for simple long root: shifts x1 by x2 and y2 by y1. -/
def unipotentLong (t : Bool) (X : SplitOctF2) : SplitOctF2 :=
  if t then
    ⟨X.a, X.b, X.x0, add2 X.x1 X.x2, X.x2, X.y0, X.y1, add2 X.y2 X.y1⟩
  else
    X

@[simp]
theorem unipotentLong_false (X : SplitOctF2) :
    unipotentLong false X = X := rfl

theorem unipotentLong_involutive (t : Bool) (X : SplitOctF2) :
    unipotentLong t (unipotentLong t X) = X := by
  cases t <;> cases X
  · rfl
  · dsimp [unipotentLong, add2]
    simp

def unipotentLongEquiv (t : Bool) : SplitOctF2 ≃ SplitOctF2 where
  toFun := unipotentLong t
  invFun := unipotentLong t
  left_inv := unipotentLong_involutive t
  right_inv := unipotentLong_involutive t

theorem unipotentLong_one (t : Bool) :
    unipotentLong t one = one := by
  cases t <;> rfl

theorem unipotentLong_add (t : Bool) (X Y : SplitOctF2) :
    unipotentLong t (add X Y) = add (unipotentLong t X) (unipotentLong t Y) := by
  cases t
  · rfl
  · rcases X with ⟨a1, b1, x01, x11, x21, y01, y11, y21⟩
    rcases Y with ⟨a2, b2, x02, x12, x22, y02, y12, y22⟩
    ext
    · rfl
    · rfl
    · rfl
    · dsimp [unipotentLong, add]
      exact xor_swap x11 x12 x21 x22
    · rfl
    · rfl
    · rfl
    · dsimp [unipotentLong, add]
      exact xor_swap y21 y22 y11 y12

theorem unipotentLong_mul (t : Bool) (X Y : SplitOctF2) :
    unipotentLong t (mul X Y) = mul (unipotentLong t X) (unipotentLong t Y) := by
  cases t
  · rfl
  · rcases X with ⟨a1, b1, x01, x11, x21, y01, y11, y21⟩
    rcases Y with ⟨a2, b2, x02, x12, x22, y02, y12, y22⟩
    ext <;>
      (try rfl) <;>
      (try {
        dsimp [unipotentLong, mul, add2, mul2, dot3, cross0, cross1, cross2]
        revert a1 a2 b1 b2 x01 x11 x21 x02 x12 x22 y01 y11 y21 y02 y12 y22
        decide
      })

/-- 🏆 THEOREM: The long root unipotent action is a genuine SplitOctF2 automorphism! -/
def unipotentLongAut (t : Bool) : SplitOctF2Aut where
  val := unipotentLongEquiv t
  property := ⟨unipotentLong_one t, unipotentLong_add t, unipotentLong_mul t⟩

/-- 🏆 THEOREM: Long root unipotent generator has order 2. -/
theorem unipotentLongAut_order (t : Bool) :
    unipotentLongAut t * unipotentLongAut t = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  intro X
  exact unipotentLong_involutive t X

end InfoGeometry.Algebra.Zorn.G2Unipotent
