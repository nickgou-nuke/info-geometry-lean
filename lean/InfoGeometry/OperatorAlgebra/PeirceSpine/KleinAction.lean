import InfoGeometry.OperatorAlgebra.PeirceSpine.UnitSquareAction
import Mathlib.GroupTheory.SpecificGroups.KleinFour
import Mathlib.Algebra.Ring.Aut
import Mathlib.Tactic.FinCases

/-! # The conditional Klein-four action on the ambient operator ring

Two commuting square-one automorphisms define a homomorphism from the
standard Klein group. Its image need not have four elements.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

private def kleinWord {G : Type*} [Group G] (a b : G)
    (z : Multiplicative (ZMod 2 × ZMod 2)) : G :=
  (if z.toAdd.1 = 0 then 1 else a) * (if z.toAdd.2 = 0 then 1 else b)

/-- The presentation by two commuting involutions, on the standard carrier. -/
def kleinHom {G : Type*} [Group G] (a b : G)
    (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a) :
    Multiplicative (ZMod 2 × ZMod 2) →* G where
  toFun := kleinWord a b
  map_one' := by simp [kleinWord]
  map_mul' := by
    have haba : a * (b * a) = b := by rw [← hab, ← mul_assoc, ha, one_mul]
    have hbab : b * (a * b) = a := by rw [hab, ← mul_assoc, hb, one_mul]
    rintro ⟨x, y⟩ ⟨z, w⟩
    change (if x + z = 0 then 1 else a) * (if y + w = 0 then 1 else b) =
      ((if x = 0 then 1 else a) * (if y = 0 then 1 else b)) *
      ((if z = 0 then 1 else a) * (if w = 0 then 1 else b))
    have cases2 (t : ZMod 2) : t = 0 ∨ t = 1 := by
      fin_cases t
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases cases2 x with rfl | rfl <;>
      rcases cases2 y with rfl | rfl <;>
      rcases cases2 z with rfl | rfl <;>
      rcases cases2 w with rfl | rfl <;>
      simp only [show (1 : ZMod 2) + 1 = 0 from rfl, add_zero, zero_add,
        show (1 : ZMod 2) ≠ 0 from by decide, ite_true, ite_false,
        mul_one, one_mul, mul_assoc, ha, hb, haba, hbab] <;>
      simp [← mul_assoc, hab] <;> simp [mul_assoc, ha]

variable {B : Type*} [Ring B] {P : B} (hP : P * P = P) (A C : B)

/-- An actual action by ring automorphisms, conditional on `V=1`. -/
def peirceKleinHom (hV : genV P A C = 1) :
    Multiplicative (ZMod 2 × ZMod 2) →* (B ≃+* B) :=
  kleinHom (phiUnitSquareEquiv hP A C hV) (parityConjRingEquiv hP)
    (by ext X; exact phiUnitSquareEquiv_involutive hP A C hV X)
    (by ext X; exact (parityConj_involutive_ring_action hP X 1).1)
    (by ext X; exact phiUnitSquareEquiv_commutes_parity hP A C hV X)

end InfoGeometry.OperatorAlgebra.PeirceSpine
