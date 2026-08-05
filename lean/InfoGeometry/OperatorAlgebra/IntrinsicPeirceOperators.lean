import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic

/-!
# Intrinsic Peirce and pair operators

This owner keeps the non-associative construction coordinate-free.  The
ambient algebra is only assumed to be a non-unital, non-associative ring; no
vector coordinates, matrix representation, dimension, or Lie-type
identification is built in.

The displayed parenthesization is part of each definition.  In particular,
the pair and outer-defect operators retain multiplication patterns instead of
collapsing them to elements of the ambient algebra.
-/

namespace InfoGeometry.OperatorAlgebra

variable {R A : Type*}
variable [Field R] [NeZero (2 : R)] [NonUnitalNonAssocRing A] [Module R A]

/-- The ordinary skew polarization of multiplication. -/
def intrinsicCommutator (x y : A) : A := x * y - y * x

/-- The ordinary symmetric polarization of multiplication. -/
def intrinsicAnticommutator (x y : A) : A := x * y + y * x

/-- The normalized Jordan polarization, when `2` is invertible in `R`. -/
def intrinsicJordanProduct (x y : A) : A :=
  (2 : R)⁻¹ • intrinsicAnticommutator x y

/-- A fixed-bracketing intrinsic triple product. -/
def intrinsicTriple (x y z : A) : A :=
  (x * y) * z + (z * y) * x

/-- The pair operator retains the triple pattern as an operator on `A`. -/
def intrinsicPairOperator (x y : A) : A → A :=
  fun z => intrinsicTriple x y z

/-- The outer-variable defect operator retains the two triple patterns. -/
def intrinsicOuterDefect (x z : A) : A → A :=
  fun y => intrinsicTriple x y z - intrinsicTriple z y x

/-- Left multiplication, retained as an operator rather than evaluated. -/
def leftAction (a : A) : A → A := fun x => a * x

/-- Right multiplication, retained as an operator rather than evaluated. -/
def rightAction (a : A) : A → A := fun x => x * a

/-- Commutator of two endomorphism-valued functions, evaluated pointwise. -/
def operatorCommutator (S T : A → A) : A → A :=
  fun x => S (T x) - T (S x)

/-- Symmetric operator polarization, evaluated pointwise. -/
def operatorAnticommutator (S T : A → A) : A → A :=
  fun x => S (T x) + T (S x)

/-- The associator, with its parenthesization made explicit. -/
def associator (a b x : A) : A := (a * b) * x - a * (b * x)

/-- Failure of left multiplication to represent the element commutator. -/
def leftActionDefect (a b : A) : A → A :=
  fun x => operatorCommutator (leftAction a) (leftAction b) x -
    leftAction (intrinsicCommutator a b) x

@[simp] theorem leftAction_apply (a x : A) : leftAction a x = a * x := rfl

@[simp] theorem rightAction_apply (a x : A) : rightAction a x = x * a := rfl

@[simp] theorem operatorCommutator_apply (S T : A → A) (x : A) :
    operatorCommutator S T x = S (T x) - T (S x) := rfl

@[simp] theorem operatorAnticommutator_apply (S T : A → A) (x : A) :
    operatorAnticommutator S T x = S (T x) + T (S x) := rfl

@[simp] theorem associator_apply (a b x : A) :
    associator a b x = (a * b) * x - a * (b * x) := rfl

@[simp] theorem intrinsicPairOperator_apply (x y z : A) :
    intrinsicPairOperator x y z = intrinsicTriple x y z := rfl

@[simp] theorem intrinsicOuterDefect_apply (x z y : A) :
    intrinsicOuterDefect x z y =
      intrinsicTriple x y z - intrinsicTriple z y x := rfl

theorem two_smul_intrinsicJordanProduct (x y : A) :
    (2 : R) • intrinsicJordanProduct (R := R) x y =
      intrinsicAnticommutator x y := by
  rw [intrinsicJordanProduct, smul_smul]
  rw [mul_inv_cancel₀ (NeZero.ne (2 : R)), one_smul]

theorem intrinsicOuterDefect_swap (x z : A) :
    intrinsicOuterDefect z x =
      fun y => -(intrinsicOuterDefect x z y) := by
  funext y
  simp only [intrinsicOuterDefect]
  abel

theorem leftActionDefect_apply (a b x : A) :
    leftActionDefect a b x = associator b a x - associator a b x := by
  simp only [leftActionDefect, operatorCommutator, leftAction,
    intrinsicCommutator, associator]
  rw [sub_mul]
  abel

end InfoGeometry.OperatorAlgebra
