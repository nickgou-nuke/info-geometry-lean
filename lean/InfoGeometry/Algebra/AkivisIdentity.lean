import Mathlib.Algebra.Ring.Associator
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Module.Basic
import Mathlib.Data.Real.Basic

namespace InfoGeometry.Algebra

variable {A : Type*} [NonUnitalNonAssocRing A]

def akivisBracket (x y : A) : A := x * y - y * x

def akivisJacobiator (x y z : A) : A :=
  akivisBracket (akivisBracket x y) z +
    akivisBracket (akivisBracket y z) x +
      akivisBracket (akivisBracket z x) y

-- Modular helper without abel
lemma akivisBracket_akivisBracket (x y z : A) :
    akivisBracket (akivisBracket x y) z =
      _root_.associator x y z - _root_.associator y x z + x * (y * z) - y * (x * z) - z * (x * y) + z * (y * x) := by
  dsimp [akivisBracket, _root_.associator_apply]
  simp only [sub_mul, mul_sub, sub_eq_add_neg]
  simp only [add_assoc, add_left_comm, add_comm]

theorem akivis_identity (x y z : A) :
    akivisJacobiator x y z =
      _root_.associator x y z + _root_.associator y z x +
        _root_.associator z x y - _root_.associator y x z -
          _root_.associator z y x - _root_.associator x z y := by
  dsimp [akivisJacobiator]
  rw [akivisBracket_akivisBracket x y z]
  rw [akivisBracket_akivisBracket y z x]
  rw [akivisBracket_akivisBracket z x y]
  simp only [sub_eq_add_neg]
  simp only [add_assoc, add_left_comm, add_comm]

def rightNestedJacobiator (x y z : A) : A :=
  akivisBracket x (akivisBracket y z) +
    akivisBracket y (akivisBracket z x) +
      akivisBracket z (akivisBracket x y)

theorem rightNestedJacobiator_eq_neg (x y z : A) :
    rightNestedJacobiator x y z = -akivisJacobiator x y z := by
  dsimp [rightNestedJacobiator, akivisJacobiator, akivisBracket]
  simp only [sub_mul, mul_sub, sub_eq_add_neg, neg_add]
  simp only [add_assoc, add_left_comm, add_comm]

theorem akivisBracket_swap (x y : A) :
    akivisBracket x y = -akivisBracket y x := by
  dsimp [akivisBracket]
  simp only [sub_eq_add_neg, neg_add, neg_neg]
  simp only [add_comm]

noncomputable def jordanChannel {A : Type*} [NonUnitalNonAssocRing A] [Module ℝ A] (x y : A) : A := (2 : ℝ)⁻¹ • (x * y + y * x)
noncomputable def lieChannel {A : Type*} [NonUnitalNonAssocRing A] [Module ℝ A] (x y : A) : A := (2 : ℝ)⁻¹ • (x * y - y * x)

theorem binary_jordan_lie_split {A : Type*} [NonUnitalNonAssocRing A] [Module ℝ A] (x y : A) : x * y = jordanChannel x y + lieChannel x y := by
  dsimp [jordanChannel, lieChannel]
  rw [← smul_add]
  have hsum : x * y + y * x + (x * y - y * x) = x * y + x * y := by
    simp only [sub_eq_add_neg]
    simp only [add_assoc, add_left_comm, add_comm]
  rw [hsum, ← two_smul ℝ (x * y), smul_smul, inv_mul_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), one_smul]

theorem jordan_lie_action_eq_chain_plus_associator {A : Type*} [NonUnitalNonAssocRing A] [Module ℝ A] (x y z : A) :
    (jordanChannel x y + lieChannel x y) * z = x * (y * z) + _root_.associator x y z := by
  rw [← binary_jordan_lie_split x y]
  dsimp [_root_.associator_apply]
  simp only [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

theorem jordan_lie_action_eq_chain_of_associator_zero {A : Type*} [NonUnitalNonAssocRing A] [Module ℝ A] (x y z : A) (hassoc : _root_.associator x y z = 0) :
    (jordanChannel x y + lieChannel x y) * z = x * (y * z) := by
  rw [jordan_lie_action_eq_chain_plus_associator x y z, hassoc, add_zero]

def leftMultiplication (x z : A) : A := x * z

def leftMultiplicationCommutatorDefect (x y z : A) : A :=
  leftMultiplication x (leftMultiplication y z) - leftMultiplication y (leftMultiplication x z) - leftMultiplication (akivisBracket x y) z

theorem leftMultiplicationCommutatorDefect_eq_associator_difference (x y z : A) :
    leftMultiplicationCommutatorDefect x y z = -_root_.associator x y z + _root_.associator y x z := by
  dsimp [leftMultiplicationCommutatorDefect, leftMultiplication, akivisBracket, _root_.associator_apply]
  simp only [sub_mul, mul_sub, sub_eq_add_neg, neg_add, neg_neg]
  simp only [add_assoc, add_left_comm, add_comm]

theorem leftMultiplicationCommutatorDefect_eq_neg_two_associator (hleft : ∀ x y z : A, _root_.associator y x z = -_root_.associator x y z) (x y z : A) :
    leftMultiplicationCommutatorDefect x y z = -(_root_.associator x y z + _root_.associator x y z) := by
  rw [leftMultiplicationCommutatorDefect_eq_associator_difference x y z, hleft x y z, neg_add]

end InfoGeometry.Algebra

