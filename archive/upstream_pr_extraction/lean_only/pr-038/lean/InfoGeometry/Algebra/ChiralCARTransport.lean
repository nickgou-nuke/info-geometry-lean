import InfoGeometry.Algebra.ChiralZornCARAndSchurBridge

/-!
# Transport of algebraic CAR relations

This file records the precise algebraic interface behind transport of a CAR
relation.  No physical interpretation is part of the theorem: the map is
only required to preserve addition, multiplication, and the unit.
-/

namespace InfoGeometry.Algebra.ChiralCARTransport

variable {A : Type*} [Ring A]
variable {B : Type*} [Ring B]

/-- A one-mode algebraic CAR packet.  This is a relation-level model, not a
physical interpretation: the carrier is any associative ring with unit. -/
structure OneModeCAR (A : Type*) [Ring A] where
  annihilator : A
  creator : A
  annihilator_sq : annihilator * annihilator = 0
  creator_sq : creator * creator = 0
  anticommutator_one :
    annihilator * creator + creator * annihilator = 1

theorem map_anticommutator_eq_of_preserving
    (U : A → A)
    (hAdd : ∀ x y, U (x + y) = U x + U y)
    (hMul : ∀ x y, U (x * y) = U x * U y)
    (hOne : U 1 = 1)
    {p q : A}
    (hCAR : p * q + q * p = 1) :
    U p * U q + U q * U p = 1 := by
  rw [← hMul p q, ← hMul q p, ← hAdd, hCAR, hOne]

theorem map_square_zero_of_preserving
    (U : A → A)
    (hMul : ∀ x y, U (x * y) = U x * U y)
    (hZero : U 0 = 0)
    {p : A}
    (hp : p * p = 0) :
    U p * U p = 0 := by
  rw [← hMul p p, hp]
  exact hZero

/-- A ring equivalence preserves the normalized one-mode CAR relation. -/
theorem ringEquiv_map_CAR
    (U : A ≃+* A) {p q : A}
    (hCAR : p * q + q * p = 1) :
    U p * U q + U q * U p = 1 := by
  rw [← U.map_mul, ← U.map_mul, ← U.map_add, hCAR, U.map_one]

/-- The CAR relation is reflected as well as preserved by a ring equivalence. -/
theorem ringEquiv_map_CAR_iff
    (U : A ≃+* B) {p q : A} :
    (U p * U q + U q * U p = 1) ↔ p * q + q * p = 1 := by
  constructor
  · intro h
    have h' := congrArg U.symm h
    simpa only [map_mul, map_add, map_one, U.symm_apply_apply] using h'
  · exact fun h => by
      rw [← U.map_mul, ← U.map_mul, ← U.map_add, h, U.map_one]

/-- A ring equivalence transports the complete one-mode CAR packet. -/
def OneModeCAR.map (U : A ≃+* B) (C : OneModeCAR A) : OneModeCAR B where
  annihilator := U C.annihilator
  creator := U C.creator
  annihilator_sq := by
    rw [← U.map_mul, C.annihilator_sq, U.map_zero]
  creator_sq := by
    rw [← U.map_mul, C.creator_sq, U.map_zero]
  anticommutator_one := by
    rw [← U.map_mul, ← U.map_mul, ← U.map_add,
      C.anticommutator_one, U.map_one]

/-- Transport through an equivalence and its inverse returns the original CAR
packet, including its distinguished generators. -/
theorem OneModeCAR.map_symm_map (U : A ≃+* B) (C : OneModeCAR A) :
    OneModeCAR.map U.symm (OneModeCAR.map U C) = C := by
  cases C with
  | mk annihilator creator annihilator_sq creator_sq anticommutator_one =>
    simp only [OneModeCAR.map]
    congr
    · exact U.symm_apply_apply annihilator
    · exact U.symm_apply_apply creator

theorem OneModeCAR.map_map_symm (U : A ≃+* B) (D : OneModeCAR B) :
    OneModeCAR.map U (OneModeCAR.map U.symm D) = D := by
  cases D with
  | mk annihilator creator annihilator_sq creator_sq anticommutator_one =>
    simp only [OneModeCAR.map]
    congr
    · exact U.apply_symm_apply annihilator
    · exact U.apply_symm_apply creator

/-- Transport through an equivalence preserves the complete CAR packet in both
directions. -/
theorem OneModeCAR.map_iff (U : A ≃+* B) (C : OneModeCAR A) (D : OneModeCAR B) :
    D = OneModeCAR.map U C ↔ OneModeCAR.map U.symm D = C := by
  constructor
  · intro h
    rw [h, OneModeCAR.map_symm_map]
  · intro h
    have h' := congrArg (OneModeCAR.map U) h
    rw [OneModeCAR.map_map_symm] at h'
    exact h'

end InfoGeometry.Algebra.ChiralCARTransport
