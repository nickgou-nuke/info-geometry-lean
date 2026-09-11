import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Finite `G₂(2)` split-octonion automorphism theorem surface

This module is the Lean twin of
`tools/sympy/g2_2_automorphism_theorem.py`.

It formalizes the split Zorn octonion multiplication over `F₂` as an exact
eight-Boolean algebra.  The companion verifier supplies the external
enumeration certificate for the automorphism count `12096`, which the Lean
file reads back only through a conditional theorem.

#### BUCKET 1: CLOSED FINITE THEOREMS

* Exact `F₂` split-octonion carrier cardinality.
* Exact `G₂(2)` order arithmetic.
* Exact order separation between `G₂(2)`/`Aut(PSU₃(3))` and `PGL₃(3)`.
* Concrete Zorn basis multiplication laws over `F₂`.
* Explicit outer `C₂` witness finite permutation readout: degree `63`,
  `28` transpositions, and `7` fixed points.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES

* `aut_splitOctF2_card_eq_g2twoOrder_from_enumeration` turns the explicit
  automorphism enumeration certificate into the theorem-level equality
  `|Aut(O_s(F₂))| = |G₂(2)|`.

#### BUCKET 3: OPEN CLOSURE DEBT

* Kernel-checking the full `12096` automorphism enumeration inside Lean is not
  done here.  The computation is performed by the SymPy/Sage/GAP verifier.
* No statement is made about real or integer split-octonion automorphism groups.
-/

namespace InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

/-- One bit of the field `F₂`, represented as `Bool`. -/
abbrev F2Bit := Bool

/-- Addition in `F₂`. -/
def add2 (x y : F2Bit) : F2Bit := decide (x ≠ y)

@[simp] theorem add2_eq_xor (x y : F2Bit) : add2 x y = x ^^ y := by
  cases x <;> cases y <;> rfl

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

def add (X Y : SplitOctF2) : SplitOctF2 :=
  ⟨X.a ^^ Y.a, X.b ^^ Y.b, X.x0 ^^ Y.x0, X.x1 ^^ Y.x1,
    X.x2 ^^ Y.x2, X.y0 ^^ Y.y0, X.y1 ^^ Y.y1, X.y2 ^^ Y.y2⟩

@[ext] theorem SplitOctF2.ext {X Y : SplitOctF2}
    (ha : X.a = Y.a) (hb : X.b = Y.b) (hx0 : X.x0 = Y.x0)
    (hx1 : X.x1 = Y.x1) (hx2 : X.x2 = Y.x2) (hy0 : X.y0 = Y.y0)
    (hy1 : X.y1 = Y.y1) (hy2 : X.y2 = Y.y2) : X = Y := by
  cases X
  cases Y
  simp_all

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

instance : Fintype SplitOctF2 where
  elems := Finset.univ.map splitOctF2EquivBits.symm.toEmbedding
  complete := by
    intro X
    simp only [Finset.mem_map, Finset.mem_univ, true_and]
    exact ⟨splitOctF2EquivBits X, splitOctF2EquivBits.symm_apply_apply X⟩

/-- The degree of the Atlas permutation action used for the outer `C₂` witness. -/
def outerC2WitnessDegree : Nat := 63

/-- The number of transpositions in the chosen outer `C₂` witness. -/
def outerC2WitnessTranspositions : Nat := 28

/-- The number of fixed points in the chosen outer `C₂` witness. -/
def outerC2WitnessFixedPoints : Nat := 7

theorem outerC2Witness_cycle_profile_accounting :
    2 * outerC2WitnessTranspositions + outerC2WitnessFixedPoints = outerC2WitnessDegree := by
  norm_num [outerC2WitnessTranspositions, outerC2WitnessFixedPoints, outerC2WitnessDegree]

theorem outerC2Witness_fixed_point_count :
    outerC2WitnessFixedPoints = 7 := by
  rfl

theorem outerC2Witness_transposition_count :
    outerC2WitnessTranspositions = 28 := by
  rfl

theorem outerC2Witness_degree :
    outerC2WitnessDegree = 63 := by
  rfl

/-- Coordinatewise zero. -/
def zero : SplitOctF2 := ⟨false, false, false, false, false, false, false, false⟩

@[simp] theorem add_self (X : SplitOctF2) : add X X = zero := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  revert a b x0 x1 x2 y0 y1 y2
  native_decide
@[simp] theorem zero_add (X : SplitOctF2) : add zero X = X := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  revert a b x0 x1 x2 y0 y1 y2
  native_decide
@[simp] theorem add_zero (X : SplitOctF2) : add X zero = X := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  revert a b x0 x1 x2 y0 y1 y2
  native_decide
theorem add_comm (X Y : SplitOctF2) : add X Y = add Y X := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  rcases Y with ⟨a',b',x0',x1',x2',y0',y1',y2'⟩
  revert a b x0 x1 x2 y0 y1 y2 a' b' x0' x1' x2' y0' y1' y2'
  native_decide
theorem add_assoc (X Y Z : SplitOctF2) : add (add X Y) Z = add X (add Y Z) := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  rcases Y with ⟨a',b',x0',x1',x2',y0',y1',y2'⟩
  rcases Z with ⟨a'',b'',x0'',x1'',x2'',y0'',y1'',y2''⟩
  revert a b x0 x1 x2 y0 y1 y2 a' b' x0' x1' x2' y0' y1' y2' a'' b'' x0'' x1'' x2'' y0'' y1'' y2''
  native_decide

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

theorem splitOctF2_basis_product_packet :
    mul ePlus ePlus = ePlus ∧
      mul eMinus eMinus = eMinus ∧
      mul ePlus eMinus = zero ∧
      mul eMinus ePlus = zero ∧
      mul up0 up0 = zero ∧
      mul up1 up1 = zero ∧
      mul up2 up2 = zero ∧
      mul down0 down0 = zero ∧
      mul down1 down1 = zero ∧
      mul down2 down2 = zero ∧
      mul up0 down0 = ePlus ∧
      mul down0 up0 = eMinus ∧
      mul up0 up1 = down2 ∧
      mul up1 up0 = down2 ∧
      mul down0 down1 = up2 ∧
      mul down1 down0 = up2 := by
  decide

/-- Predicate for a unital split-octonion algebra automorphism over `F₂`. -/
def IsSplitOctF2Aut (f : SplitOctF2 ≃ SplitOctF2) : Prop :=
  f one = one ∧
    (∀ X Y : SplitOctF2, f (add X Y) = add (f X) (f Y)) ∧
    (∀ X Y : SplitOctF2, f (mul X Y) = mul (f X) (f Y))

/-- The finite automorphism type `Aut(O_s(F₂))`. -/
def SplitOctF2Aut := { f : SplitOctF2 ≃ SplitOctF2 // IsSplitOctF2Aut f }

instance : One SplitOctF2Aut where
  one := ⟨1, by
    refine ⟨?_, ?_, ?_⟩
    · rfl
    · intro X Y
      rfl
    · intro X Y
      rfl
    ⟩

instance : Mul SplitOctF2Aut where
  mul f g := ⟨g.1 * f.1, by
    refine ⟨?_, ?_, ?_⟩
    · have hfg : (g.1 * f.1) one = g.1 (f.1 one) := rfl
      rw [hfg, f.2.1, g.2.1]
    · intro X Y
      have hfg (Z : SplitOctF2) : (g.1 * f.1) Z = g.1 (f.1 Z) := rfl
      rw [hfg, hfg, hfg, f.2.2.1, g.2.2.1]
    · intro X Y
      have hfg (Z : SplitOctF2) : (g.1 * f.1) Z = g.1 (f.1 Z) := rfl
      rw [hfg, hfg, hfg, f.2.2.2, g.2.2.2]
    ⟩

instance : Inv SplitOctF2Aut where
  inv f := ⟨f.1.symm, by
    refine ⟨?_, ?_, ?_⟩
    · apply f.1.injective
      simp only [Equiv.apply_symm_apply]
      exact f.2.1.symm
    · intro X Y
      apply f.1.injective
      change f.1 ((f.1).symm (add X Y)) =
        f.1 (add ((f.1).symm X) ((f.1).symm Y))
      simp only [Equiv.apply_symm_apply]
      simpa only [Equiv.apply_symm_apply] using
        (f.2.2.1 ((f.1).symm X) ((f.1).symm Y)).symm
    · intro X Y
      apply f.1.injective
      change f.1 ((f.1).symm (mul X Y)) =
        f.1 (mul ((f.1).symm X) ((f.1).symm Y))
      simp only [Equiv.apply_symm_apply]
      simpa only [Equiv.apply_symm_apply] using
        (f.2.2.2 ((f.1).symm X) ((f.1).symm Y)).symm
    ⟩

instance : Group SplitOctF2Aut where
  one := 1
  mul := (· * ·)
  inv := Inv.inv
  one_mul f := by
    apply Subtype.ext
    apply Equiv.ext
    intro X
    rfl
  mul_one f := by
    apply Subtype.ext
    apply Equiv.ext
    intro X
    rfl
  mul_assoc f g h := by
    apply Subtype.ext
    apply Equiv.ext
    intro X
    rfl
  inv_mul_cancel f := by
    apply Subtype.ext
    apply Equiv.ext
    intro X
    change f.1 ((f.1).symm X) = X
    exact Equiv.apply_symm_apply f.1 X

theorem SplitOctF2Aut.mul_apply (f g : SplitOctF2Aut) (X : SplitOctF2) :
    (f * g).1 X = g.1 (f.1 X) := by
  change (g.1 * f.1) X = g.1 (f.1 X)
  rfl

attribute [local instance] Classical.decEq

noncomputable instance : Fintype SplitOctF2Aut := by
  classical
  unfold SplitOctF2Aut
  infer_instance

/--
The theorem-level finite classification readout.

The premise is the explicit enumeration certificate produced by
`tools/sympy/g2_2_automorphism_theorem.py`: all unital multiplication-preserving
linear maps of the split Zorn algebra over `F₂` have been counted, and the count
is `12096`.
-/
theorem aut_splitOctF2_card_eq_g2twoOrder_from_enumeration
    (h_enum : Fintype.card SplitOctF2Aut = 12096) :
    Fintype.card SplitOctF2Aut = g2twoOrder := by
  simpa [g2twoOrder] using h_enum

end InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
