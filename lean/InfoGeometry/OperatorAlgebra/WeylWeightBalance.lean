import Mathlib.Tactic
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.OperatorAlgebra.WeylWeightBalance

Pure Weyl-weight and mode-balance bookkeeping.

This module is intentionally weaker than a five-graded Lie-algebra theorem.  It
does not assert bracket closure, Sugawara, Virasoro central terms, Tomita sign
reversal, or anomaly cancellation.

It only formalizes the reusable algebraic rule:

```text
balanced total weight or balanced total mode routes to the invariant sector.
```

Concrete multiplication, bracket, current, or Virasoro laws are external
predicates supplied by owner modules.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.WeylWeightBalance

/-! ## 1. Five Weyl weights -/

/-- Five Weyl grades used by the projective/lightcone/affine readout system. -/
@[rep_depth operator]
inductive FiveGrade where
  | m2
  | m1
  | zero
  | p1
  | p2
deriving DecidableEq, Repr

namespace FiveGrade

/-- Integer Weyl weight of a five-grade symbol. -/
@[rep_depth operator]
def weight : FiveGrade → ℤ
  | m2 => -2
  | m1 => -1
  | zero => 0
  | p1 => 1
  | p2 => 2

@[rep_depth operator, simp]
theorem weight_m2 :
    weight m2 = -2 := rfl

@[rep_depth operator, simp]
theorem weight_m1 :
    weight m1 = -1 := rfl

@[rep_depth operator, simp]
theorem weight_zero :
    weight zero = 0 := rfl

@[rep_depth operator, simp]
theorem weight_p1 :
    weight p1 = 1 := rfl

@[rep_depth operator, simp]
theorem weight_p2 :
    weight p2 = 2 := rfl

/-- Two grades are balanced exactly when their integer weights sum to zero. -/
@[rep_depth operator]
def Balanced (a b : FiveGrade) : Prop :=
  weight a + weight b = 0

@[rep_depth operator]
theorem p2_m2_balanced :
    Balanced p2 m2 := by
  rfl

@[rep_depth operator]
theorem m2_p2_balanced :
    Balanced m2 p2 := by
  rfl

@[rep_depth operator]
theorem p1_m1_balanced :
    Balanced p1 m1 := by
  rfl

@[rep_depth operator]
theorem m1_p1_balanced :
    Balanced m1 p1 := by
  rfl

@[rep_depth operator]
theorem zero_zero_balanced :
    Balanced zero zero := by
  rfl

end FiveGrade

/-! ## 2. Carrier and external predicates -/

/--
A readout/object with an assigned Weyl grade.

No multiplication, bracket, or physical law is bundled here.
-/
@[rep_depth operator]
structure WeylGradedCarrier
    (Obj : Type*) where
  gradeOf : Obj → FiveGrade

/-- External predicate: two objects have balanced Weyl weights. -/
@[rep_depth operator]
def IsWeylBalanced
    {Obj : Type*}
    (G : WeylGradedCarrier Obj)
    (x y : Obj) : Prop :=
  FiveGrade.weight (G.gradeOf x) + FiveGrade.weight (G.gradeOf y) = 0

/-- External predicate: an object is a physical grade-zero readout. -/
@[rep_depth operator]
def IsPhysicalGradeZero
    {Obj : Type*}
    (G : WeylGradedCarrier Obj)
    (x : Obj) : Prop :=
  FiveGrade.weight (G.gradeOf x) = 0

/--
External predicate: multiplication adds integer Weyl weights.

This is not true for arbitrary carriers, so it is never bundled into
`WeylGradedCarrier`.
-/
@[rep_depth operator]
def IsAdditiveWeightForMul
    {Obj : Type*} [Mul Obj]
    (G : WeylGradedCarrier Obj) : Prop :=
  ∀ x y : Obj,
    FiveGrade.weight (G.gradeOf (x * y)) =
      FiveGrade.weight (G.gradeOf x) + FiveGrade.weight (G.gradeOf y)

/--
Balanced factors multiply to a grade-zero readout whenever multiplication adds
weights.
-/
@[rep_depth operator]
theorem mul_is_physical_of_balanced
    {Obj : Type*} [Mul Obj]
    (G : WeylGradedCarrier Obj)
    (hMul : IsAdditiveWeightForMul G)
    {x y : Obj}
    (hBal : IsWeylBalanced G x y) :
    IsPhysicalGradeZero G (x * y) := by
  unfold IsPhysicalGradeZero IsWeylBalanced at *
  rw [hMul x y]
  exact hBal

/-! ## 3. Bracket and mode balance sockets -/

/--
External predicate: a bracket-like operation adds integer Weyl weights.

This covers Lie brackets, superbrackets, commutators, and graded current
brackets once a concrete owner supplies the law.
-/
@[rep_depth operator]
def IsAdditiveWeightForBracket
    {Obj BracketOut : Type*}
    (G : WeylGradedCarrier Obj)
    (H : WeylGradedCarrier BracketOut)
    (bracket : Obj → Obj → BracketOut) : Prop :=
  ∀ x y : Obj,
    FiveGrade.weight (H.gradeOf (bracket x y)) =
      FiveGrade.weight (G.gradeOf x) + FiveGrade.weight (G.gradeOf y)

/--
Balanced inputs bracket to a grade-zero readout whenever the bracket adds
weights.
-/
@[rep_depth operator]
theorem bracket_is_physical_of_balanced
    {Obj BracketOut : Type*}
    (G : WeylGradedCarrier Obj)
    (H : WeylGradedCarrier BracketOut)
    (bracket : Obj → Obj → BracketOut)
    (hBracket : IsAdditiveWeightForBracket G H bracket)
    {x y : Obj}
    (hBal : IsWeylBalanced G x y) :
    IsPhysicalGradeZero H (bracket x y) := by
  unfold IsPhysicalGradeZero IsWeylBalanced at *
  rw [hBracket x y]
  exact hBal

/-- Virasoro/affine mode balance: a central mode term can only be selected at `m+n=0`. -/
@[rep_depth operator]
def IsModeBalanced
    (m n : ℤ) : Prop :=
  m + n = 0

@[rep_depth operator]
theorem modeBalanced_comm
    {m n : ℤ}
    (h : IsModeBalanced m n) :
    IsModeBalanced n m := by
  unfold IsModeBalanced at *
  simpa [add_comm] using h

/--
If a mode-dependent central selector is explicitly gated by `m+n=0`, then it
vanishes outside the balanced sector.
-/
@[rep_depth operator]
theorem centralSelector_eq_zero_of_not_modeBalanced
    {Central : Type*} [Zero Central]
    (selector : ℤ → ℤ → Central)
    (hSelector : ∀ m n : ℤ, ¬ IsModeBalanced m n → selector m n = 0)
    {m n : ℤ}
    (hNot : ¬ IsModeBalanced m n) :
    selector m n = 0 :=
  hSelector m n hNot

end InfoGeometry.OperatorAlgebra.WeylWeightBalance
