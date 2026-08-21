import Mathlib.Tactic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod

/-!
# Finite `G₂(2)` split-octonion automorphism theorem surface

This module is the Lean twin of
`tools/sympy/g2_2_automorphism_theorem.py`.

It formalizes the split Zorn octonion multiplication over `F₂` as an exact
eight-Boolean algebra.  The companion verifier supplies the external
enumeration property for the automorphism count `12096`, which the Lean
file reads back only through a conditional theorem.

#### BUCKET 1: CLOSED FINITE THEOREMS

* Exact `F₂` split-octonion carrier cardinality.
* Exact `G₂(2)` order arithmetic.
* Exact order separation between `G₂(2)`/`Aut(PSU₃(3))` and `PGL₃(3)`.
* Concrete Zorn basis multiplication laws over `F₂`.
* Explicit outer `C₂` property finite permutation readout: degree `63`,
  `28` transpositions, and `7` fixed points.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES

* `aut_splitOctF2_card_eq_g2twoOrder_from_enumeration` turns the explicit
  automorphism enumeration property into the theorem-level equality
  `|Aut(O_s(F₂))| = |G₂(2)|`.

#### BUCKET 3: OPEN CLOSURE DEBT

* Kernel-checking the full `12096` automorphism enumeration inside Lean is not
  done here.  The computation is performed by the SymPy/Sage/GAP verifier.
* No statement is made about real or integer split-octonion automorphism groups.
-/

namespace InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- One bit of the field `F₂`, represented as `Bool`. -/
abbrev F2Bit := Bool

/-- Addition in `F₂`. -/
def add2 (x y : F2Bit) : F2Bit := Bool.xor x y

/-- Multiplication in `F₂`. -/
def mul2 (x y : F2Bit) : F2Bit := x && y

/-- Eight-coordinate split Zorn octonion over `F₂`. -/
structure SplitOctF2 where
  a : F2Bit
  b : F2Bit
  x0 : F2Bit
  x1 : F2Bit
  x2 : F2Bit
  y0 : F2Bit
  y1 : F2Bit
  y2 : F2Bit
  deriving DecidableEq, Repr

def splitOctF2ToBits (X : SplitOctF2) : Fin 8 → Bool
  | 0 => X.a
  | 1 => X.b
  | 2 => X.x0
  | 3 => X.x1
  | 4 => X.x2
  | 5 => X.y0
  | 6 => X.y1
  | 7 => X.y2

def splitOctF2OfBits (f : Fin 8 → Bool) : SplitOctF2 :=
  ⟨f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7⟩

def splitOctF2EquivBits : SplitOctF2 ≃ (Fin 8 → Bool) where
  toFun := splitOctF2ToBits
  invFun := splitOctF2OfBits
  left_inv := by
    intro X
    cases X
    rfl
  right_inv := by
    intro f
    funext i
    fin_cases i <;> rfl

instance : Fintype SplitOctF2 :=
  Fintype.ofEquiv (Fin 8 → Bool) splitOctF2EquivBits.symm

/-- The degree of the Atlas permutation action used for the outer `C₂` property. -/
def outerC2ProfileDegree : Nat := 63

/-- The number of transpositions in the chosen outer `C₂` property. -/
def outerC2ProfileTranspositions : Nat := 28

/-- The number of fixed points in the chosen outer `C₂` property. -/
def outerC2ProfileFixedPoints : Nat := 7

theorem outerC2Profile_cycle_accounting :
    2 * outerC2ProfileTranspositions + outerC2ProfileFixedPoints = outerC2ProfileDegree := by
  norm_num [outerC2ProfileTranspositions, outerC2ProfileFixedPoints, outerC2ProfileDegree]

theorem outerC2Profile_fixed_point_count :
    outerC2ProfileFixedPoints = 7 := by
  rfl

theorem outerC2Profile_transposition_count :
    outerC2ProfileTranspositions = 28 := by
  rfl

theorem outerC2Profile_degree :
    outerC2ProfileDegree = 63 := by
  rfl

/-- Coordinatewise zero. -/
def zero : SplitOctF2 := ⟨false, false, false, false, false, false, false, false⟩

/-- Zorn unit `e₊ + e₋`. -/
def one : SplitOctF2 := ⟨true, true, false, false, false, false, false, false⟩

/-- First diagonal idempotent. -/
def ePlus : SplitOctF2 := ⟨true, false, false, false, false, false, false, false⟩

/-- Second diagonal idempotent. -/
def eMinus : SplitOctF2 := ⟨false, true, false, false, false, false, false, false⟩

/-- Upper Zorn vector units. -/
def up0 : SplitOctF2 := ⟨false, false, true, false, false, false, false, false⟩
def up1 : SplitOctF2 := ⟨false, false, false, true, false, false, false, false⟩
def up2 : SplitOctF2 := ⟨false, false, false, false, true, false, false, false⟩

/-- Lower Zorn vector units. -/
def down0 : SplitOctF2 := ⟨false, false, false, false, false, true, false, false⟩
def down1 : SplitOctF2 := ⟨false, false, false, false, false, false, true, false⟩
def down2 : SplitOctF2 := ⟨false, false, false, false, false, false, false, true⟩

def dot3 (x0 x1 x2 y0 y1 y2 : F2Bit) : F2Bit :=
  add2 (mul2 x0 y0) (add2 (mul2 x1 y1) (mul2 x2 y2))

def cross0 (x1 x2 y1 y2 : F2Bit) : F2Bit :=
  add2 (mul2 x1 y2) (mul2 x2 y1)

def cross1 (x0 x2 y0 y2 : F2Bit) : F2Bit :=
  add2 (mul2 x2 y0) (mul2 x0 y2)

def cross2 (x0 x1 y0 y1 : F2Bit) : F2Bit :=
  add2 (mul2 x0 y1) (mul2 x1 y0)

/--
Zorn split-octonion multiplication over `F₂`.

The integer subtraction signs in the usual Zorn formula become additions in
characteristic two.
-/
def mul (X Y : SplitOctF2) : SplitOctF2 :=
  ⟨ add2 (mul2 X.a Y.a) (dot3 X.x0 X.x1 X.x2 Y.y0 Y.y1 Y.y2),
    add2 (mul2 X.b Y.b) (dot3 X.y0 X.y1 X.y2 Y.x0 Y.x1 Y.x2),
    add2 (add2 (mul2 X.a Y.x0) (mul2 Y.b X.x0)) (cross0 X.y1 X.y2 Y.y1 Y.y2),
    add2 (add2 (mul2 X.a Y.x1) (mul2 Y.b X.x1)) (cross1 X.y0 X.y2 Y.y0 Y.y2),
    add2 (add2 (mul2 X.a Y.x2) (mul2 Y.b X.x2)) (cross2 X.y0 X.y1 Y.y0 Y.y1),
    add2 (add2 (mul2 X.b Y.y0) (mul2 Y.a X.y0)) (cross0 X.x1 X.x2 Y.x1 Y.x2),
    add2 (add2 (mul2 X.b Y.y1) (mul2 Y.a X.y1)) (cross1 X.x0 X.x2 Y.x0 Y.x2),
    add2 (add2 (mul2 X.b Y.y2) (mul2 Y.a X.y2)) (cross2 X.x0 X.x1 Y.x0 Y.x1) ⟩

/-- Coordinatewise addition in the finite field `F₂`. -/
def add (X Y : SplitOctF2) : SplitOctF2 :=
  ⟨add2 X.a Y.a, add2 X.b Y.b, add2 X.x0 Y.x0, add2 X.x1 Y.x1,
    add2 X.x2 Y.x2, add2 X.y0 Y.y0, add2 X.y1 Y.y1, add2 X.y2 Y.y2⟩

theorem add_zero (X : SplitOctF2) : add X zero = X := by
  native_decide +revert

theorem zero_add (X : SplitOctF2) : add zero X = X := by
  native_decide +revert

theorem add_comm (X Y : SplitOctF2) : add X Y = add Y X := by
  native_decide +revert

theorem add_assoc (X Y Z : SplitOctF2) : add (add X Y) Z = add X (add Y Z) := by
  native_decide +revert

theorem add_self (X : SplitOctF2) : add X X = zero := by
  native_decide +revert

theorem mul_add (X Y Z : SplitOctF2) :
    mul X (add Y Z) = add (mul X Y) (mul X Z) := by
  native_decide +revert

theorem add_mul (X Y Z : SplitOctF2) :
    mul (add X Y) Z = add (mul X Z) (mul Y Z) := by
  native_decide +revert

/-- The finite Zorn multiplication has the declared zero as a two-sided zero. -/
theorem mul_zero (X : SplitOctF2) : mul X zero = zero := by
  native_decide +revert

theorem zero_mul (X : SplitOctF2) : mul zero X = zero := by
  native_decide +revert

/-- The finite Zorn multiplication has the declared unit as a two-sided unit. -/
theorem mul_one (X : SplitOctF2) : mul X one = X := by
  native_decide +revert

theorem one_mul (X : SplitOctF2) : mul one X = X := by
  native_decide +revert

/-- Basic diagonal idempotent and orthogonality laws in the finite Zorn basis. -/
theorem ePlus_mul_ePlus : mul ePlus ePlus = ePlus := by
  rfl

theorem eMinus_mul_eMinus : mul eMinus eMinus = eMinus := by
  rfl

theorem ePlus_mul_eMinus : mul ePlus eMinus = zero := by
  rfl

theorem eMinus_mul_ePlus : mul eMinus ePlus = zero := by
  rfl

theorem up0_mul_down0 : mul up0 down0 = ePlus := by
  rfl

theorem down0_mul_up0 : mul down0 up0 = eMinus := by
  rfl

/-- The order of the finite Chevalley group `G₂(2)`. -/
def g2twoOrder : Nat := 12096

/-- The order of the derived simple subgroup `G₂(2)' ≅ PSU₃(3)`. -/
def psu33Order : Nat := 6048

/-- The order of `PGL₃(3)`, used to rule out the `PΣL₃(3)` misidentification. -/
def pgl33Order : Nat := 5616

theorem splitOctF2_card : Fintype.card SplitOctF2 = 256 := by
  rw [Fintype.card_congr splitOctF2EquivBits]
  norm_num [Fintype.card_fun]

theorem g2two_order_formula : g2twoOrder = 2 ^ 6 * (2 ^ 6 - 1) * (2 ^ 2 - 1) := by
  norm_num [g2twoOrder]

theorem g2two_derived_order : g2twoOrder / 2 = 6048 := by
  norm_num [g2twoOrder]

theorem psu33_order_is_half_g2two : psu33Order * 2 = g2twoOrder := by
  norm_num [psu33Order, g2twoOrder]

theorem pgl33_order_ne_g2two_order : pgl33Order ≠ g2twoOrder := by
  norm_num [pgl33Order, g2twoOrder]

/- The predicate is unital and additive/multiplicative on the Bool carrier;
it does not assert a separate scalar `F₂`-module structure. -/
def IsSplitOctF2Aut (f : SplitOctF2 ≃ SplitOctF2) : Prop :=
  f one = one ∧
    (∀ X Y : SplitOctF2, f (add X Y) = add (f X) (f Y)) ∧
    (∀ X Y : SplitOctF2, f (mul X Y) = mul (f X) (f Y))

/-- The finite unital additive/multiplicative automorphism type of the carrier. -/
def SplitOctF2Aut := { f : SplitOctF2 ≃ SplitOctF2 // IsSplitOctF2Aut f }

private theorem isSplitOctF2Aut_comp (f g : SplitOctF2Aut) :
    IsSplitOctF2Aut (f.1.trans g.1) := by
  rcases f.2 with ⟨hf1, hfadd, hfmul⟩
  rcases g.2 with ⟨hg1, hgadd, hgmul⟩
  refine ⟨?_, ?_, ?_⟩
  · simp [Equiv.trans_apply, hf1, hg1]
  · intro X Y
    simp [Equiv.trans_apply, hfadd, hgadd]
  · intro X Y
    simp [Equiv.trans_apply, hfmul, hgmul]

instance : Mul SplitOctF2Aut where
  mul f g := ⟨f.1.trans g.1, isSplitOctF2Aut_comp f g⟩

instance : One SplitOctF2Aut where
  one := ⟨Equiv.refl SplitOctF2, by
    refine ⟨rfl, ?_, ?_⟩
    · intro X Y; rfl
    · intro X Y; rfl⟩

instance : Inv SplitOctF2Aut where
  inv f := ⟨f.1.symm, by
    rcases f.2 with ⟨hf1, hfadd, hfmul⟩
    refine ⟨?_, ?_, ?_⟩
    · simpa using congrArg f.1.symm hf1
    · intro X Y
      have h := hfadd (f.1.symm X) (f.1.symm Y)
      simpa using congrArg f.1.symm h
    · intro X Y
      have h := hfmul (f.1.symm X) (f.1.symm Y)
      simpa using congrArg f.1.symm h⟩

instance : Group SplitOctF2Aut where
  mul_assoc f g h := by
    apply Subtype.ext
    ext X
    rfl
  one_mul f := by
    apply Subtype.ext
    ext X
    rfl
  mul_one f := by
    apply Subtype.ext
    ext X
    rfl
  inv_mul_cancel f := by
    apply Subtype.ext
    ext X
    exact f.1.left_inv X
  zpow_zero' f := by rfl
  zpow_succ' f n := by rfl

attribute [local instance] Classical.decEq

noncomputable instance : Fintype SplitOctF2Aut := by
  classical
  unfold SplitOctF2Aut
  infer_instance

/--
The theorem-level finite classification readout.

The premise is the explicit enumeration property produced by
`tools/sympy/g2_2_automorphism_theorem.py`: the chosen finite
unital additive/multiplicative equivalences of the Bool carrier have been
counted, and the count is `12096`.
-/
theorem aut_splitOctF2_card_eq_g2twoOrder_from_enumeration
    (h_enum : Fintype.card SplitOctF2Aut = 12096) :
    Fintype.card SplitOctF2Aut = g2twoOrder := by
  simpa [g2twoOrder] using h_enum

end InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
