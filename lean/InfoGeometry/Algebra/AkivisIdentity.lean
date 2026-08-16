import Mathlib.Algebra.Ring.Associator
import Mathlib.Algebra.Module.Basic
import Mathlib.Data.Real.Basic

/-!
# The generic Akivis identity

This is the universal binary/ternary identity attached to a non-associative
ring.  It assumes neither alternativity nor a Malcev structure.
-/

namespace InfoGeometry.Algebra

variable {A : Type*} [NonUnitalNonAssocRing A]

def akivisBracket (x y : A) : A := x * y - y * x

def akivisJacobiator (x y z : A) : A :=
  akivisBracket (akivisBracket x y) z +
    akivisBracket (akivisBracket y z) x +
      akivisBracket (akivisBracket z x) y

theorem akivis_identity (x y z : A) :
    akivisJacobiator x y z =
      _root_.associator x y z + _root_.associator y z x +
        _root_.associator z x y - _root_.associator y x z -
          _root_.associator z y x - _root_.associator x z y := by
  simp [akivisJacobiator, akivisBracket, _root_.associator_apply,
    sub_eq_add_neg, mul_add, add_mul]
  abel

def rightNestedJacobiator (x y z : A) : A :=
  akivisBracket x (akivisBracket y z) +
    akivisBracket y (akivisBracket z x) +
      akivisBracket z (akivisBracket x y)

theorem rightNestedJacobiator_eq_neg (x y z : A) :
    rightNestedJacobiator x y z = -akivisJacobiator x y z := by
  simp [rightNestedJacobiator, akivisJacobiator, akivisBracket]
  abel_nf

theorem akivisBracket_swap (x y : A) :
    akivisBracket x y = -akivisBracket y x := by
  simp [akivisBracket]

/-! ## Normalized Jordan/Lie channels and the associator action defect -/

noncomputable def jordanChannel {A : Type*} [NonUnitalNonAssocRing A] [Module ℝ A]
    (x y : A) : A :=
  (2 : ℝ)⁻¹ • (x * y + y * x)

noncomputable def lieChannel {A : Type*} [NonUnitalNonAssocRing A] [Module ℝ A]
    (x y : A) : A :=
  (2 : ℝ)⁻¹ • (x * y - y * x)

theorem binary_jordan_lie_split
    {A : Type*} [NonUnitalNonAssocRing A] [Module ℝ A]
    (x y : A) :
    x * y = jordanChannel x y + lieChannel x y := by
  dsimp [jordanChannel, lieChannel]
  rw [← smul_add]
  have hsum :
      x * y + y * x + (x * y - y * x) = x * y + x * y := by
    abel
  rw [hsum, ← two_smul ℝ (x * y), smul_smul]
  rw [inv_mul_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), one_smul]

theorem jordan_lie_action_eq_chain_plus_associator
    {A : Type*} [NonUnitalNonAssocRing A] [Module ℝ A]
    (x y z : A) :
    (jordanChannel x y + lieChannel x y) * z =
      x * (y * z) + _root_.associator x y z := by
  rw [← binary_jordan_lie_split x y]
  simp only [_root_.associator_apply]
  abel

theorem jordan_lie_action_eq_chain_of_associator_zero
    {A : Type*} [NonUnitalNonAssocRing A] [Module ℝ A]
    (x y z : A) (hassoc : _root_.associator x y z = 0) :
    (jordanChannel x y + lieChannel x y) * z = x * (y * z) := by
  rw [jordan_lie_action_eq_chain_plus_associator x y z, hassoc, add_zero]

def leftMultiplication (x z : A) : A := x * z

def leftMultiplicationCommutatorDefect (x y z : A) : A :=
  leftMultiplication x (leftMultiplication y z) -
    leftMultiplication y (leftMultiplication x z) -
      leftMultiplication (akivisBracket x y) z

theorem leftMultiplicationCommutatorDefect_eq_associator_difference
    (x y z : A) :
    leftMultiplicationCommutatorDefect x y z =
      -_root_.associator x y z + _root_.associator y x z := by
  simp [leftMultiplicationCommutatorDefect, leftMultiplication,
    akivisBracket, _root_.associator_apply, sub_eq_add_neg, mul_add,
    add_mul]
  abel

/-- Under the explicit alternative-law consequence
`A(y,x,z) = -A(x,y,z)`, the representation defect is `-2 A(x,y,z)`.
Alternativity is intentionally a hypothesis here; it is not inferred for an
operator-valued Zorn carrier. -/
theorem leftMultiplicationCommutatorDefect_eq_neg_two_associator
    (hleft : ∀ x y z : A,
      _root_.associator y x z = -_root_.associator x y z)
    (x y z : A) :
    leftMultiplicationCommutatorDefect x y z =
      -(_root_.associator x y z + _root_.associator x y z) := by
  calc
    leftMultiplicationCommutatorDefect x y z =
        -_root_.associator x y z + _root_.associator y x z :=
      leftMultiplicationCommutatorDefect_eq_associator_difference x y z
    _ = -_root_.associator x y z + -_root_.associator x y z := by
      rw [hleft x y z]
    _ = -(_root_.associator x y z + _root_.associator x y z) := by
      rw [neg_add]

end InfoGeometry.Algebra
