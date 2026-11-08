import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.NuclearOperatorSuperSoloviev

/-!
# Typed `ℤ₂` superalgebra interface

The operator super-Soloviev owner proves the parity multiplication table.
This module packages that table as a typed degree calculus.

For homogeneous elements, degree multiplication is addition mod two:

* even·even = even
* even·odd = odd
* odd·even = odd
* odd·odd = even

The superbracket is the ordinary commutator unless both inputs are odd, in
which case it is the anticommutator.  Its output is proved homogeneous of the
product degree.
-/

noncomputable section

namespace InfoGeometry.Physics.NuclearZ2Superalgebra

open InfoGeometry.Physics.NuclearOperatorSuperSoloviev

variable {A : Type*} [Ring A]

/-- Two parity degrees. -/
inductive Degree where
  | even
  | odd
  deriving DecidableEq, Repr

namespace Degree

/-- Multiplication/addition mod two of parity degrees. -/
def mul : Degree → Degree → Degree
  | .even, d => d
  | .odd, .even => .odd
  | .odd, .odd => .even

@[simp] theorem even_mul (d : Degree) : mul .even d = d := rfl
@[simp] theorem mul_even (d : Degree) : mul d .even = d := by cases d <;> rfl
@[simp] theorem odd_mul_odd : mul .odd .odd = .even := rfl

/-- Parity multiplication is associative. -/
theorem mul_assoc (a b c : Degree) :
    mul (mul a b) c = mul a (mul b c) := by
  cases a <;> cases b <;> cases c <;> rfl

end Degree

/-- Homogeneity predicate selected by a parity degree. -/
def Homogeneous (P : InternalParity A) : Degree → A → Prop
  | .even, x => P.IsEven x
  | .odd, x => P.IsOdd x

@[simp] theorem homogeneous_even_iff (P : InternalParity A) (x : A) :
    Homogeneous P .even x ↔ P.IsEven x := Iff.rfl

@[simp] theorem homogeneous_odd_iff (P : InternalParity A) (x : A) :
    Homogeneous P .odd x ↔ P.IsOdd x := Iff.rfl

/-- Product of homogeneous elements has the product parity degree. -/
theorem homogeneous_mul
    (P : InternalParity A)
    {p q : Degree} {x y : A}
    (hx : Homogeneous P p x) (hy : Homogeneous P q y) :
    Homogeneous P (Degree.mul p q) (x * y) := by
  cases p <;> cases q
  · exact P.even_mul_even hx hy
  · exact P.even_mul_odd hx hy
  · exact P.odd_mul_even hx hy
  · exact P.odd_mul_odd hx hy

/-- Odd-even ordinary commutators remain odd. -/
theorem odd_comm_even
    (P : InternalParity A) {x y : A}
    (hx : P.IsOdd x) (hy : P.IsEven y) :
    P.IsOdd (InternalParity.comm x y) := by
  unfold InternalParity.comm InternalParity.IsOdd
  simp only [sub_eq_add_neg, P.act_add, P.act_neg, P.act_mul]
  rw [hx, hy]
  noncomm_ring

/-- The superbracket: odd/odd uses the anticommutator; all other degree pairs
use the ordinary commutator. -/
def superBracket : Degree → Degree → A → A → A
  | .odd, .odd, x, y => InternalParity.anticomm x y
  | _, _, x, y => InternalParity.comm x y

/-- The superbracket of homogeneous elements has the product degree. -/
theorem superBracket_homogeneous
    (P : InternalParity A)
    {p q : Degree} {x y : A}
    (hx : Homogeneous P p x) (hy : Homogeneous P q y) :
    Homogeneous P (Degree.mul p q) (superBracket p q x y) := by
  cases p <;> cases q
  · exact P.even_comm_even hx hy
  · exact P.even_comm_odd hx hy
  · exact odd_comm_even P hx hy
  · exact P.odd_anticomm_odd hx hy

/-- Explicit homogeneous multiplication packet for all four parity cases. -/
theorem degree_table_packet
    (P : InternalParity A)
    {e0 e1 o0 o1 : A}
    (he0 : Homogeneous P .even e0)
    (he1 : Homogeneous P .even e1)
    (ho0 : Homogeneous P .odd o0)
    (ho1 : Homogeneous P .odd o1) :
    Homogeneous P .even (e0 * e1) ∧
      Homogeneous P .odd (e0 * o0) ∧
      Homogeneous P .odd (o0 * e0) ∧
      Homogeneous P .even (o0 * o1) :=
  ⟨homogeneous_mul P he0 he1,
    homogeneous_mul P he0 ho0,
    homogeneous_mul P ho0 he0,
    homogeneous_mul P ho0 ho1⟩

end InfoGeometry.Physics.NuclearZ2Superalgebra

end noncomputable section
