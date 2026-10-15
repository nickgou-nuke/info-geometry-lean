import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Algebra.Basic

/-!
# Split Involution and Peirce Projectors

This file implements the algebraic mechanics of a split involution (\(\epsilon^2 = 1\))
and its associated Peirce projectors (\(P_\pm = \frac{1 \pm \epsilon}{2}\)).

It proves the existence and uniqueness of the associated module decomposition
(chiral splitting), isolating the purely algebraic properties independent of
topological or geometric interpretations.

All theorems are formally verified in native Mathlib.
-/

namespace InfoGeometry.GrandUnification.ArchetypeDictionary

variable {R A : Type*} [CommRing R] [Invertible (2 : R)] [Ring A] [Algebra R A]

/-- The positive Peirce operator associated to an element of a unital algebra. -/
def peircePlus (epsilon : A) : A := (⅟(2 : R)) • (1 + epsilon)

/-- The negative Peirce operator associated to an element of a unital algebra. -/
def peirceMinus (epsilon : A) : A := (⅟(2 : R)) • (1 - epsilon)

/-- Direct projector completeness theorem: only the operator equation
`epsilon * epsilon = 1` is used; no splitting package is required. -/
theorem peircePlus_add_peirceMinus (epsilon : A) :
    peircePlus (R := R) epsilon + peirceMinus (R := R) epsilon = 1 := by
  dsimp [peircePlus, peirceMinus]
  rw [← smul_add]
  have h_sum : (1 : A) + epsilon + ((1 : A) - epsilon) = (2 : R) • (1 : A) := by
    calc
      (1 : A) + epsilon + ((1 : A) - epsilon) = (1 : A) + 1 := by noncomm_ring
      _ = (2 : R) • (1 : A) := by rw [two_smul]
  rw [h_sum, ← mul_smul, invOf_mul_self, one_smul]

/-- The difference of the two Peirce projectors recovers the involution. -/
theorem peircePlus_sub_peirceMinus (epsilon : A) :
    peircePlus (R := R) epsilon - peirceMinus (R := R) epsilon = epsilon := by
  dsimp [peircePlus, peirceMinus]
  rw [← smul_sub]
  have h_diff : (1 : A) + epsilon - ((1 : A) - epsilon) = (2 : R) • epsilon := by
    calc
      (1 : A) + epsilon - ((1 : A) - epsilon) = epsilon + epsilon := by noncomm_ring
      _ = (2 : R) • epsilon := by rw [two_smul]
  rw [h_diff, smul_smul, invOf_mul_self, one_smul]

/-- Direct idempotence theorem for the positive Peirce operator. -/
theorem peircePlus_sq (epsilon : A) (hε : epsilon * epsilon = 1) :
    peircePlus (R := R) epsilon * peircePlus (R := R) epsilon =
      peircePlus (R := R) epsilon := by
  dsimp [peircePlus]
  rw [smul_mul_smul]
  have h_sq : (1 + epsilon) * (1 + epsilon) = (2 : R) • (1 + epsilon) := by
    calc
      (1 + epsilon) * (1 + epsilon) = 1 + epsilon + epsilon + epsilon * epsilon := by noncomm_ring
      _ = 1 + epsilon + epsilon + 1 := by rw [hε]
      _ = (1 + epsilon) + (1 + epsilon) := by abel
      _ = (2 : R) • (1 + epsilon) := by rw [two_smul]
  rw [h_sq, ← mul_smul]
  have h_coeff : (⅟(2 : R) * ⅟(2 : R)) * 2 = ⅟(2 : R) := by
    calc
      (⅟(2 : R) * ⅟(2 : R)) * 2 = ⅟(2 : R) * (⅟(2 : R) * 2) := by rw [mul_assoc]
      _ = ⅟(2 : R) * 1 := by rw [invOf_mul_self]
      _ = ⅟(2 : R) := by rw [mul_one]
  rw [h_coeff]

/-- Direct idempotence theorem for the negative Peirce operator. -/
theorem peirceMinus_sq (epsilon : A) (hε : epsilon * epsilon = 1) :
    peirceMinus (R := R) epsilon * peirceMinus (R := R) epsilon =
      peirceMinus (R := R) epsilon := by
  dsimp [peirceMinus]
  rw [smul_mul_smul]
  have h_sq : (1 - epsilon) * (1 - epsilon) = (2 : R) • (1 - epsilon) := by
    calc
      (1 - epsilon) * (1 - epsilon) = 1 - epsilon - epsilon + epsilon * epsilon := by noncomm_ring
      _ = 1 - epsilon - epsilon + 1 := by rw [hε]
      _ = (1 - epsilon) + (1 - epsilon) := by abel
      _ = (2 : R) • (1 - epsilon) := by rw [two_smul]
  rw [h_sq, ← mul_smul]
  have h_coeff : (⅟(2 : R) * ⅟(2 : R)) * 2 = ⅟(2 : R) := by
    calc
      (⅟(2 : R) * ⅟(2 : R)) * 2 = ⅟(2 : R) * (⅟(2 : R) * 2) := by rw [mul_assoc]
      _ = ⅟(2 : R) * 1 := by rw [invOf_mul_self]
      _ = ⅟(2 : R) := by rw [mul_one]
  rw [h_coeff]

/-- Direct cross-annihilation of the Peirce operators in either order. -/
theorem peircePlus_mul_peirceMinus (epsilon : A) (hε : epsilon * epsilon = 1) :
    peircePlus (R := R) epsilon * peirceMinus (R := R) epsilon = 0 := by
  dsimp [peircePlus, peirceMinus]
  rw [smul_mul_smul]
  have h_cross : (1 + epsilon) * (1 - epsilon) = 0 := by
    calc
      (1 + epsilon) * (1 - epsilon) = 1 - epsilon * epsilon := by noncomm_ring
      _ = 1 - 1 := by rw [hε]
      _ = 0 := by noncomm_ring
  rw [h_cross, smul_zero]

/-- Reverse-order cross-annihilation for the Peirce operators. -/
theorem peirceMinus_mul_peircePlus (epsilon : A) (hε : epsilon * epsilon = 1) :
    peirceMinus (R := R) epsilon * peircePlus (R := R) epsilon = 0 := by
  dsimp [peircePlus, peirceMinus]
  rw [smul_mul_smul]
  have h_cross : (1 - epsilon) * (1 + epsilon) = 0 := by
    calc
      (1 - epsilon) * (1 + epsilon) = 1 - epsilon * epsilon := by noncomm_ring
      _ = 1 - 1 := by rw [hε]
      _ = 0 := by noncomm_ring
  rw [h_cross, smul_zero]

structure SplitInvolution (R A : Type*) [CommRing R] [Invertible (2 : R)] [Ring A] [Algebra R A] where
  epsilon : A
  sq_eq_one : epsilon * epsilon = 1

namespace SplitInvolution

variable (inv : SplitInvolution R A)

def P_plus : A := peircePlus (R := R) inv.epsilon
def P_minus : A := peirceMinus (R := R) inv.epsilon

theorem P_plus_add_P_minus : inv.P_plus + inv.P_minus = 1 := by
  exact peircePlus_add_peirceMinus (R := R) inv.epsilon

theorem P_plus_sq : inv.P_plus * inv.P_plus = inv.P_plus := by
  exact peircePlus_sq (R := R) inv.epsilon inv.sq_eq_one

theorem P_minus_sq : inv.P_minus * inv.P_minus = inv.P_minus := by
  exact peirceMinus_sq (R := R) inv.epsilon inv.sq_eq_one

theorem P_plus_mul_P_minus : inv.P_plus * inv.P_minus = 0 := by
  exact peircePlus_mul_peirceMinus (R := R) inv.epsilon inv.sq_eq_one

theorem P_minus_mul_P_plus : inv.P_minus * inv.P_plus = 0 := by
  exact peirceMinus_mul_peircePlus (R := R) inv.epsilon inv.sq_eq_one

variable {M : Type*} [AddCommGroup M] [Module A M]

def chiral_plus (x : M) : M := inv.P_plus • x
def chiral_minus (x : M) : M := inv.P_minus • x

theorem chiral_plus_add_chiral_minus (x : M) : inv.chiral_plus x + inv.chiral_minus x = x := by
  dsimp [chiral_plus, chiral_minus]
  rw [← add_smul, P_plus_add_P_minus, one_smul]

theorem chiral_plus_idempotent (x : M) : inv.chiral_plus (inv.chiral_plus x) = inv.chiral_plus x := by
  dsimp [chiral_plus]
  rw [smul_smul, P_plus_sq]

theorem chiral_minus_idempotent (x : M) : inv.chiral_minus (inv.chiral_minus x) = inv.chiral_minus x := by
  dsimp [chiral_minus]
  rw [smul_smul, P_minus_sq]

theorem chiral_minus_plus_zero (x : M) : inv.chiral_minus (inv.chiral_plus x) = 0 := by
  dsimp [chiral_minus, chiral_plus]
  rw [smul_smul, P_minus_mul_P_plus, zero_smul]

theorem chiral_plus_minus_zero (x : M) : inv.chiral_plus (inv.chiral_minus x) = 0 := by
  dsimp [chiral_minus, chiral_plus]
  rw [smul_smul, P_plus_mul_P_minus, zero_smul]

theorem chiral_plus_add (x y : M) : inv.chiral_plus (x + y) = inv.chiral_plus x + inv.chiral_plus y := by
  dsimp [chiral_plus]
  rw [smul_add]

theorem chiral_minus_add (x y : M) : inv.chiral_minus (x + y) = inv.chiral_minus x + inv.chiral_minus y := by
  dsimp [chiral_minus]
  rw [smul_add]

/-- The decomposition into chiral components is unique. -/
theorem chiral_decomposition_unique (x a b : M)
    (ha : inv.chiral_plus a = a)
    (hb : inv.chiral_minus b = b)
    (hsum : x = a + b) :
    a = inv.chiral_plus x ∧ b = inv.chiral_minus x := by
  constructor
  · calc
      a = a + 0 := by rw [add_zero]
      _ = inv.chiral_plus a + 0 := by rw [ha]
      _ = inv.chiral_plus a + inv.chiral_plus b := by
          have hz : inv.chiral_plus b = 0 := by
            rw [← hb, chiral_plus_minus_zero]
          rw [hz]
      _ = inv.chiral_plus (a + b) := (chiral_plus_add inv a b).symm
      _ = inv.chiral_plus x := by rw [← hsum]
  · calc
      b = 0 + b := by rw [zero_add]
      _ = 0 + inv.chiral_minus b := by rw [hb]
      _ = inv.chiral_minus a + inv.chiral_minus b := by
          have hz : inv.chiral_minus a = 0 := by
            rw [← ha, chiral_minus_plus_zero]
          rw [hz]
      _ = inv.chiral_minus (a + b) := (chiral_minus_add inv a b).symm
      _ = inv.chiral_minus x := by rw [← hsum]

/-- Certified archetype extraction for Peirce projector laws in any associative algebra. -/
theorem dischargePeirce :
    inv.P_plus + inv.P_minus = 1 ∧
    inv.P_plus * inv.P_plus = inv.P_plus ∧
    inv.P_minus * inv.P_minus = inv.P_minus ∧
    inv.P_plus * inv.P_minus = 0 ∧
    inv.P_minus * inv.P_plus = 0 :=
  ⟨inv.P_plus_add_P_minus, inv.P_plus_sq, inv.P_minus_sq,
   inv.P_plus_mul_P_minus, inv.P_minus_mul_P_plus⟩

end SplitInvolution
end InfoGeometry.GrandUnification.ArchetypeDictionary
