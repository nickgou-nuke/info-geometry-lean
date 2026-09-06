import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Hom.Defs

/-!
# Minimal Multiplicative Congruence Compatibility Layer

This replaces the old copied Lean-3 congruence file with the small API used by
`PresentedMonoid_mine`.
-/

variable {M N : Type*}

/-- A multiplicative congruence relation. -/
structure Con' (M : Type*) [Mul M] where
  rel : M → M → Prop
  iseqv : Equivalence rel
  mul' : ∀ {a b c d : M}, rel a b → rel c d → rel (a * c) (b * d)

namespace Con'

instance [Mul M] : CoeFun (Con' M) (fun _ => M → M → Prop) where
  coe c := c.rel

theorem refl [Mul M] (c : Con' M) (a : M) : c a a := c.iseqv.refl a
theorem symm [Mul M] (c : Con' M) {a b : M} (h : c a b) : c b a := c.iseqv.symm h
theorem trans [Mul M] (c : Con' M) {a b d : M} (h₁ : c a b) (h₂ : c b d) : c a d :=
  c.iseqv.trans h₁ h₂
theorem mul [Mul M] (c : Con' M) {a b d e : M} : c a b → c d e → c (a * d) (b * e) :=
  c.mul'

def toSetoid [Mul M] (c : Con' M) : Setoid M where
  r := c.rel
  iseqv := c.iseqv

/-- Quotient by a multiplicative congruence. -/
abbrev Quotient [Mul M] (c : Con' M) : Type _ :=
  _root_.Quotient c.toSetoid

instance [Mul M] (c : Con' M) : Mul c.Quotient where
  mul x y :=
    _root_.Quotient.liftOn₂ x y
      (fun a b => _root_.Quotient.mk c.toSetoid (a * b))
      (by
        intro a₁ a₂ b₁ b₂ ha hb
        exact _root_.Quotient.sound (c.mul ha hb))

theorem quotient_mk_mul [Mul M] (c : Con' M) (a b : M) :
    (_root_.Quotient.mk c.toSetoid (a * b) : c.Quotient) =
      ((_root_.Quotient.mk c.toSetoid a : c.Quotient) *
        (_root_.Quotient.mk c.toSetoid b : c.Quotient)) := rfl

instance [Monoid M] (c : Con' M) : One c.Quotient where
  one := _root_.Quotient.mk c.toSetoid 1

instance monoid [Monoid M] (c : Con' M) : Monoid c.Quotient where
  one_mul := by
    intro x
    exact _root_.Quotient.inductionOn x (fun a =>
      congrArg (_root_.Quotient.mk c.toSetoid) (one_mul a))
  mul_one := by
    intro x
    exact _root_.Quotient.inductionOn x (fun a =>
      congrArg (_root_.Quotient.mk c.toSetoid) (mul_one a))
  mul_assoc := by
    intro x y z
    exact _root_.Quotient.inductionOn₃ x y z (fun a b d =>
      congrArg (_root_.Quotient.mk c.toSetoid) (mul_assoc a b d))

def liftOn [Mul M] {β : Type*} {c : Con' M} (q : c.Quotient) (f : M → β)
    (h : ∀ a b, c a b → f a = f b) : β :=
  _root_.Quotient.liftOn q f h

def lift [Monoid M] [Monoid N] (c : Con' M) (f : M →* N)
    (h : ∀ a b, c a b → f a = f b) : c.Quotient →* N where
  toFun q := liftOn q f h
  map_one' := by
    change f 1 = 1
    exact f.map_one
  map_mul' := by
    intro x y
    exact _root_.Quotient.inductionOn₂ x y (fun a b => by
      change f (a * b) = f a * f b
      exact f.map_mul a b)

@[simp] theorem lift_mk' [Monoid M] [Monoid N] {c : Con' M} {f : M →* N}
    (h : ∀ a b, c a b → f a = f b) (x : M) :
    lift c f h (_root_.Quotient.mk c.toSetoid x) = f x := by
  change f x = f x
  rfl

end Con'

namespace Con'Gen

variable [Mul M] (r : M → M → Prop)

/-- Generated congruence relation from a raw relation. -/
inductive Rel : M → M → Prop
  | of (a b : M) : r a b → Rel a b
  | refl (a : M) : Rel a a
  | symm {a b : M} : Rel a b → Rel b a
  | trans {a b c : M} : Rel a b → Rel b c → Rel a c
  | mul {a b c d : M} : Rel a b → Rel c d → Rel (a * c) (b * d)

end Con'Gen

open Con'Gen

def con'Gen [Mul M] (r : M → M → Prop) : Con' M where
  rel := Con'Gen.Rel r
  iseqv := {
    refl := Con'Gen.Rel.refl
    symm := fun h => Con'Gen.Rel.symm h
    trans := fun h₁ h₂ => Con'Gen.Rel.trans h₁ h₂
  }
  mul' := fun h₁ h₂ => Con'Gen.Rel.mul h₁ h₂

namespace Con'

variable [Mul M]

theorem con'Gen_le {r : M → M → Prop} {s : M → M → Prop}
    (h : ∀ a b, r a b → s a b)
    (hRefl : ∀ a, s a a)
    (hSymm : ∀ {a b}, s a b → s b a)
    (hTrans : ∀ {a b c}, s a b → s b c → s a c)
    (hMul : ∀ {a b c d}, s a b → s c d → s (a * c) (b * d)) :
    ∀ a b, con'Gen r a b → s a b := by
  intro a b hr
  induction hr with
  | of a b hab => exact h a b hab
  | refl a => exact hRefl a
  | symm hab ih => exact hSymm ih
  | trans hab hbc ihab ihbc => exact hTrans ihab ihbc
  | mul hab hcd ihab ihcd => exact hMul ihab ihcd

end Con'
