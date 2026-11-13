/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.SplitAtomDoubling
import InfoGeometry.Algebra.QuaternionCayleyPair

/-!
# Four split generators and their quaternion pair over arbitrary coefficients

The native matrix doubling owner constructs every generator used here.
Its `negative` is the negative of the intake's `Omega`, so the displayed
generators have signs `(+1, -1, +1, -1)` in that convention.

The two negative-square generators and their product satisfy the quaternion
relations. This is a statement inside `M₂(M₂(B))` for an arbitrary ring `B`;
it asserts no Clifford universal equivalence, real compactness, or linear
independence. In particular `B` may itself be an unrestricted endomorphism ring.
-/

namespace InfoGeometry.Clifford.SplitAtomQuaternion

open InfoGeometry.Clifford.SplitAtomDoubling
open InfoGeometry.Algebra.QuaternionCayleyPair

variable {B : Type*} [Ring B]

/-- The attachment's four gamma operators, indexed from zero. -/
def gamma : Fin 4 → Block2 (Block2 B) :=
  ![(positive : Block2 (Block2 B)), -negative,
    twisted (positive : Block2 B), twisted (-(negative : Block2 B))]

/-- The split square relations follow from the existing doubling maps. -/
theorem gamma_square (k : Fin 4) :
    gamma (B := B) k * gamma k = (![1, -1, 1, -1] : Fin 4 → Block2 (Block2 B)) k := by
  fin_cases k
  · change (positive : Block2 (Block2 B)) * positive = 1
    exact positive_square
  · change (-(negative : Block2 (Block2 B))) * (-negative) = -1
    simpa only [neg_mul_neg] using (negative_square (A := Block2 B))
  · change twisted (positive : Block2 B) * twisted positive = 1
    rw [twisted_mul, positive_square]
    exact (repeatedHom (A := Block2 B)).map_one
  · change twisted (-(negative : Block2 B)) * twisted (-negative) = -1
    rw [twisted_mul, neg_mul_neg, negative_square]
    change (repeatedHom (A := Block2 B)) (-1) = -1
    simp

private theorem signed_head_anticommutator {A : Type*} [Ring A] :
    (positive : Block2 A) * (-negative) + (-negative) * positive = 0 := by
  simpa only [mul_neg, neg_mul, neg_add, neg_zero] using
    congrArg (fun x : Block2 A => -x) (head_anticommutator (A := A))

/-- The four nested generators anticommute without commuting coefficients. -/
theorem gamma_anticommutator (r s : Fin 4) (hrs : r ≠ s) :
    gamma (B := B) r * gamma s + gamma s * gamma r = 0 := by
  have h01 : gamma (B := B) 0 * gamma 1 + gamma 1 * gamma 0 = 0 :=
    signed_head_anticommutator
  have h02 : gamma (B := B) 0 * gamma 2 + gamma 2 * gamma 0 = 0 := by
    change positive * twisted (positive : Block2 B) + twisted positive * positive = 0
    simpa only [add_comm] using twisted_positive_anticommutator (positive : Block2 B)
  have h03 : gamma (B := B) 0 * gamma 3 + gamma 3 * gamma 0 = 0 := by
    change positive * twisted (-(negative : Block2 B)) + twisted (-negative) * positive = 0
    simpa only [add_comm] using twisted_positive_anticommutator (-(negative : Block2 B))
  have h12 : gamma (B := B) 1 * gamma 2 + gamma 2 * gamma 1 = 0 := by
    change (-negative) * twisted (positive : Block2 B) + twisted positive * (-negative) = 0
    have h := congrArg (fun x : Block2 (Block2 B) => -x)
      (twisted_negative_anticommutator (positive : Block2 B))
    simpa only [neg_add, neg_zero, mul_neg, neg_mul, add_comm] using h
  have h13 : gamma (B := B) 1 * gamma 3 + gamma 3 * gamma 1 = 0 := by
    change (-negative) * twisted (-(negative : Block2 B)) + twisted (-negative) * (-negative) = 0
    have h := congrArg (fun x : Block2 (Block2 B) => -x)
      (twisted_negative_anticommutator (-(negative : Block2 B)))
    simpa only [neg_add, neg_zero, mul_neg, neg_mul, add_comm] using h
  have h23 : gamma (B := B) 2 * gamma 3 + gamma 3 * gamma 2 = 0 := by
    change twisted (positive : Block2 B) * twisted (-negative) +
      twisted (-negative) * twisted positive = 0
    rw [twisted_anticommutator, signed_head_anticommutator]
    exact (repeatedHom (A := Block2 B)).map_zero
  fin_cases r <;> fin_cases s
  · exact False.elim (hrs rfl)
  · exact h01
  · exact h02
  · exact h03
  · exact (add_comm _ _).trans h01
  · exact False.elim (hrs rfl)
  · exact h12
  · exact h13
  · exact (add_comm _ _).trans h02
  · exact (add_comm _ _).trans h12
  · exact False.elim (hrs rfl)
  · exact h23
  · exact (add_comm _ _).trans h03
  · exact (add_comm _ _).trans h13
  · exact (add_comm _ _).trans h23
  · exact False.elim (hrs rfl)

/-- First quaternion axis: the second split generator. -/
abbrev firstAxis : Block2 (Block2 B) := gamma 1

/-- Second quaternion axis: the fourth split generator. -/
abbrev secondAxis : Block2 (Block2 B) := gamma 3

/-- Third quaternion axis: the ordered product, with no scalar replacement. -/
abbrev thirdAxis : Block2 (Block2 B) := firstAxis * secondAxis

theorem firstAxis_square : (firstAxis : Block2 (Block2 B)) * firstAxis = -1 :=
  gamma_square 1

theorem secondAxis_square : (secondAxis : Block2 (Block2 B)) * secondAxis = -1 :=
  gamma_square 3

theorem first_second_anticommutator :
    (firstAxis : Block2 (Block2 B)) * secondAxis + secondAxis * firstAxis = 0 :=
  gamma_anticommutator 1 3 (by decide)

theorem thirdAxis_square : (thirdAxis : Block2 (Block2 B)) * thirdAxis = -1 :=
  product_square firstAxis_square secondAxis_square first_second_anticommutator

theorem first_second_commutator :
    (firstAxis : Block2 (Block2 B)) * secondAxis - secondAxis * firstAxis = 2 * thirdAxis :=
  InfoGeometry.Algebra.QuaternionCayleyPair.first_second_commutator first_second_anticommutator

theorem second_third_commutator :
    (secondAxis : Block2 (Block2 B)) * thirdAxis - thirdAxis * secondAxis = 2 * firstAxis :=
  second_product_commutator secondAxis_square first_second_anticommutator

theorem third_first_commutator :
    (thirdAxis : Block2 (Block2 B)) * firstAxis - firstAxis * thirdAxis = 2 * secondAxis :=
  product_first_commutator firstAxis_square first_second_anticommutator

/-- The division-free Cayley quarter-turn, with the exact scale factor. -/
theorem firstAxis_cayley_sandwich :
    (1 + (firstAxis : Block2 (Block2 B))) * secondAxis * (1 - firstAxis) = 2 * thirdAxis :=
  cayley_sandwich firstAxis_square first_second_anticommutator

end InfoGeometry.Clifford.SplitAtomQuaternion
